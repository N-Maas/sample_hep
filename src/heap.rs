use crate::{groups::*, params::*, primitives::*};
use rand::{Rng, SeedableRng};
use rand_pcg::Pcg32;
use smallvec::SmallVec;
use std::{iter, iter::FromIterator, mem};

type Rand = Pcg32;

// TODO replace Iterator with IntoIter in arguments

// TODO: implement Clone?
// TODO: try to reduce size a bit?
#[derive(Debug)]
pub struct SampleHeap<T: Ord + Clone> {
    len: usize,
    insertion_heap: BufferHeap<T>,
    groups: Groups<T>,
}

impl<T: Ord + Clone> SampleHeap<T> {
    pub fn new() -> Self {
        Self {
            len: 0,
            insertion_heap: BufferHeap::new(),
            groups: Groups {
                rng: Rand::from_seed([0; 16]),
                r_distr: RDistribute::new(),
                deletion_heap: BufferHeap::new(),
                group_list: SmallVec::new(),
            },
        }
    }

    pub fn is_empty(&self) -> bool {
        let result = self.len == 0;
        // TODO: remove this when sufficiently tested
        debug_assert!(
            self.insertion_heap.is_empty()
                && self.groups.deletion_heap.is_empty()
                && self.groups.group_list.iter().all(|g| g.is_empty()) == result
        );
        result
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.groups.deletion_heap.is_empty() {
            self.groups.refill_deletion_heap();
        }

        let del = self.groups.deletion_heap.peek();
        let ins = self.insertion_heap.peek();
        let remove_from_del_heap = match (del, ins) {
            (Some(a), Some(b)) => a < b,
            (Some(_), None) => true,
            _ => false,
        };

        let result = if remove_from_del_heap {
            self.groups.deletion_heap.pop()
        } else {
            self.insertion_heap.pop()
        };
        if result.is_some() {
            self.len -= 1;
        }
        result
    }

    pub fn push(&mut self, el: T) {
        self.insertion_heap
            .push(el)
            .unwrap_or_else(|HeapOverflowError(remaining)| {
                // The remaining element should not be appended to the iterator, because this would an unnecessary
                // overflow of the deletion heap when emptying the insertion heap for the first time.
                self.groups.insert_all(self.insertion_heap.drain());
                // can not fail as the heap was emptied
                self.insertion_heap.push(remaining).ok().unwrap();
            });
        self.len += 1;
    }
}

#[derive(Debug)]
struct Groups<T: Ord + Clone> {
    rng: Rand,
    r_distr: RDistribute<T>,
    deletion_heap: BufferHeap<T>,
    // note that a BufferedGroup is really large and thus moves should be avoided
    // (around 3/6 KByte for i32/i64)
    group_list: SmallVec<[Box<BufferedGroup<T>>; 5]>,
}

impl<T: Ord + Clone> Groups<T> {
    fn refill_deletion_heap(&mut self) {
        todo!();
    }

    // TODO: structure checks
    fn insert_all(&mut self, iter: impl Iterator<Item = T>) {
        for el in iter {
            let idx = self.r_distr.distribute(&el);
            if idx == 0 {
                self.deletion_heap
                    .push(el)
                    .unwrap_or_else(|err| self.handle_deletion_heap_overflow(err.0))
            } else {
                let group_idx = idx - 1;
                let group = self.group_list[group_idx].as_mut();
                Self::resolve_overflow(group.push(el))
                    .map(|seq_idx| self.handle_group_overflow(group_idx, seq_idx));
            }
        }

        debug_assert!(self.structure_check());
    }

    /// Insertion into an existing group. Each sequence except the first must be associated to a larger splitter.
    /// For the first sequence, the according splitter from the RDistribute is used.
    /// Thus, the number of splitter must be one less then the number of sequences.
    fn insert_sequences_to_group(
        &mut self,
        group_idx: usize,
        splitter: T,
        splitters: impl Iterator<Item = T>,
        seqs: impl Iterator<Item = Sequence<T>>,
    ) {
        debug_assert!(group_idx < self.group_list.len());
        debug_assert!(splitter <= *self.r_distr.splitter_at(group_idx));

        let first_splitter = self.r_distr.replace_splitter(splitter, group_idx);
        let mut iter = splitters.chain(iter::once(first_splitter)).zip(seqs);

        // push new sequences to the group
        let group = &mut self.group_list[group_idx];
        let max_seq_len = group.max_seq_len();
        for (splitter, mut seq) in &mut iter {
            if group.num_sequences() == _K {
                break;
            }

            // TODO: What is the right strategy for filling a group?
            // Maybe sequence should be filled only to half?
            let first_seq = group.first_or_insert();
            if first_seq.len() + seq.len() <= max_seq_len {
                first_seq.append(&mut seq);
            } else {
                group.push_sequence(splitter, seq);
            }
        }

        // if the group is full, append to the first sequence
        let first_seq = group.first_or_insert();
        for (_, ref mut seq) in iter {
            first_seq.append(seq);
        }
        if first_seq.len() > max_seq_len {
            self.handle_group_overflow(group_idx, 0);
        }

        debug_assert!(self.structure_check());
    }

    // TODO: use quickselect or a sampled element instead of sorting?
    fn handle_deletion_heap_overflow(&mut self, remaining: T) {
        let max_seq_len = _M;

        let mut elements: Vec<T> = self
            .deletion_heap
            .drain()
            .chain(iter::once(remaining))
            .collect();
        elements.sort();
        debug_assert!(elements.len() == _M + 1);

        if self.group_list.is_empty() {
            // if the first group does not exist yet, initialize it from the deletion heap
            let step = (_M + 1) as f64 / (_K + 1) as f64;
            let first = step.round() as usize;
            self.r_distr.add_splitter(elements[first].clone());

            let splitters: Vec<T> = (2..=_K)
                .map(|i| elements[(i as f64 * step).round() as usize].clone())
                .collect();
            let mut base_group = BaseGroup::new(max_seq_len, &splitters);
            base_group.forced_insert_all(elements.drain(first..elements.len()));
            self.group_list
                .push(Box::new(BufferedGroup::from_base_group(base_group)));
        } else {
            // otherwise, push half of the elements into the first group
            let mid = elements.len() / 2;
            let splitter = elements[mid].clone();
            let seq = Sequence::from_iter(elements.drain((mid + 1)..elements.len()));
            self.insert_sequences_to_group(0, splitter, None.into_iter(), iter::once(seq));
        }

        for el in elements.into_iter() {
            // can not fail as the heap was emptied
            self.deletion_heap.push(el).ok().unwrap();
        }

        debug_assert!(self.structure_check());
    }

    fn handle_group_overflow(&mut self, group_idx: usize, seq_idx: usize) {
        todo!();
    }

    /// used for checking invariants
    pub fn structure_check(&self) -> bool {
        assert_eq!(self.group_list.len(), self.r_distr.len());

        let mut valid = self.r_distr.structure_check();
        let mut prev_max = self.deletion_heap.max();
        for (i, group) in self.group_list.iter().enumerate() {
            let splitter = self.r_distr.splitter_at(i);
            valid &= group.structure_check();
            valid &= prev_max.map_or(true, |m| m <= splitter);
            valid &= group.min().map_or(true, |m| splitter <= m);
            prev_max = group.max()
        }
        valid
    }

    /// If an error occurs, returns the index of the overflowing sequence.
    fn resolve_overflow<R, I: Iterator<Item = T>>(
        result: Result<R, GroupOverflowError<T, I>>,
    ) -> Option<usize> {
        result
            .err()
            // the two steps are necessary to correctly resolve the lifetimes
            .map(
                |GroupOverflowError {
                     base_group,
                     seq_idx,
                     remaining,
                 }| {
                    base_group.forced_insert_all(remaining);
                    seq_idx
                },
            )
    }

    // TODO: fix
    fn choose_sample<'a>(rng: &mut Rand, elements: &'a [T]) -> &'a [T] {
        let num_steps = (elements.len() - 1) / _SAMPLING;
        dbg!(num_steps); // -
        dbg!(elements.len()); // -

        let step_idx = rng.gen_range(0, num_steps);
        let start = _SAMPLING * step_idx;
        &elements[start..(start + _SAMPLING)]
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_heaps_only() {
        let mut s_heap = SampleHeap::new();

        for i in 0..(2 * _M) {
            assert_eq!(i, s_heap.len());
            s_heap.push(i);
        }
        assert!(s_heap.groups.structure_check());
        for i in 0.._M {
            assert_eq!(Some(i), s_heap.pop());
        }
        assert_eq!(_M, s_heap.len());
    }

    #[test]
    fn test_deletion_heap_overflow() {
        let mut s_heap = SampleHeap::new();

        for i in (0.._M).chain((0.._M).rev()).chain(0..=_M) {
            s_heap.push(i);
        }
        assert!(s_heap.groups.structure_check());
    }
}
