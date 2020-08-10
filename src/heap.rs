use crate::{dbg_assertion, groups::*, params::*, primitives::*};
use arrayvec::ArrayVec;
use rand::{Rng, SeedableRng};
use rand_pcg::Pcg32;
use smallvec::SmallVec;
use std::{fmt::Debug, iter, iter::FromIterator, mem};

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
        debug_assert!(self.deletion_heap.is_empty());
        if self.group_list.is_empty() {
            return;
        }

        if let Some(mut seq) = self.pull_non_empty_sequence(0) {
            for el in seq.drain() {
                // can not fail as one sequence of the first group always fits into the heap
                self.deletion_heap.push(el).ok().unwrap()
            }
        }

        dbg_assertion!(self.structure_check());
    }

    fn refill_group(&mut self, group_idx: usize) {
        debug_assert!(self.group_list[group_idx].is_empty());
        if group_idx + 1 == self.group_list.len() {
            return;
        }

        let max_seq_len = self.group_list[group_idx + 1].max_seq_len();
        if let Some(seq) = self.pull_non_empty_sequence(group_idx + 1) {
            let base_group = self.group_list[group_idx].base_group();
            Self::refill_group_from_sequence(
                &mut self.rng,
                base_group,
                seq,
                &base_group.min_splitter().clone(),
            );

            Self::scan_and_split(&mut self.rng, base_group).map(|(mut splitters, sequences)| {
                // can not fail because scan_and_split does not return an empty iterator
                let splitter = splitters.next().unwrap();

                // edge case: last group was removed by pull_non_empty_sequence
                if group_idx + 1 == self.group_list.len() {
                    // TODO: group cache
                    self.group_list
                        .push(Box::new(BufferedGroup::new(max_seq_len, splitter.clone())));
                    self.r_distr.add_splitter(splitter.clone());
                }
                self.insert_sequences_to_group(
                    group_idx + 1,
                    splitter,
                    splitters.rev(),
                    sequences.rev(),
                );
            });
        }

        dbg_assertion!(self.structure_check());
    }

    /// Tries to retrieve a sequence from the group with the given index,
    /// recursively calling refill_group if necessary. Additionally adjusts the splitters.
    fn pull_non_empty_sequence(&mut self, group_idx: usize) -> Option<Sequence<T>> {
        debug_assert!(group_idx < self.group_list.len());

        let base_group = self.clear_and_handle_overflow(group_idx);
        if base_group.is_empty() {
            self.refill_group(group_idx);
        }

        let base_group = self.group_list[group_idx].base_group();
        while let (splitter, Some(seq)) = base_group.pop_sequence() {
            if seq.len() > 0 {
                match splitter {
                    Some(s) => Some(s),
                    None => {
                        if self.r_distr.len() == group_idx + 1 {
                            // TODO: cache groups to avoid unnecessary allocation?
                            self.group_list.pop();
                            self.r_distr.remove_splitter();
                            None
                        } else {
                            Some(self.r_distr.splitter_at(group_idx + 1).clone())
                        }
                    }
                }
                .map(|splitter| {
                    self.r_distr.replace_splitter(splitter, group_idx);
                });
                return Some(seq);
            }
        }
        None
    }

    fn clear_and_handle_overflow(&mut self, group_idx: usize) -> &mut BaseGroup<T> {
        debug_assert!(group_idx < self.group_list.len());

        if let Some(seq_idx) = Self::resolve_overflow(self.group_list[group_idx].clear_buffer()) {
            self.handle_group_overflow(group_idx, seq_idx);
        }
        self.group_list[group_idx].base_group()
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

        dbg_assertion!(self.structure_check());
    }

    /// Insertion into an existing group. Each sequence except the first must be associated to a larger splitter.
    /// For the first sequence, the according splitter from the RDistribute is used.
    /// Thus, the number of splitter must be one less then the number of sequences.
    ///
    /// Order: The splitters and sequences must be in decreasing order (order of insertion).
    fn insert_sequences_to_group(
        &mut self,
        group_idx: usize,
        splitter: T,
        splitters: impl Iterator<Item = T>,
        sequences: impl Iterator<Item = Sequence<T>>,
    ) {
        // TODO: incorrect order?!
        debug_assert!(group_idx < self.group_list.len());
        debug_assert!(splitter <= *self.r_distr.splitter_at(group_idx));

        let first_splitter = self.r_distr.replace_splitter(splitter, group_idx);
        let iter = splitters.chain(iter::once(first_splitter)).zip(sequences);

        // push new sequences to the group
        let group = &mut self.group_list[group_idx];
        let max_seq_len = group.max_seq_len();
        for (splitter, mut seq) in iter {
            let num_seqs = group.num_sequences();

            // TODO: What is the right strategy for filling a group?
            // Maybe sequences should be filled only to half?
            let first_seq = group.first_or_insert();
            if num_seqs == _K || first_seq.len() + seq.len() <= max_seq_len {
                first_seq.append(&mut seq);
            } else {
                group.push_sequence(splitter, seq);
            }
        }

        // handle overflow
        if group.first_or_insert().len() > max_seq_len {
            self.handle_group_overflow(group_idx, 0);
        }

        dbg_assertion!(self.structure_check());
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

        dbg_assertion!(self.structure_check());
    }

    fn handle_group_overflow(&mut self, group_idx: usize, seq_idx: usize) {
        debug_assert!(group_idx < self.group_list.len() && seq_idx < _K);
        let num_groups = self.group_list.len();
        let base_group = self.group_list[group_idx].clear_buffer_forced();
        let max_seq_len = base_group.max_seq_len();

        // split the overflowing sequence, removing the biggest sequence from the group
        let (big_splitter, big_sequence) = Self::split_in_two(&mut self.rng, base_group, seq_idx)
            .map_or((None, None), |(s, seq)| (Some(s), Some(seq)));
        let n_skip = _K - base_group.num_sequences();

        // can not fail as at least one sequence is present
        let elements = base_group.pop_sequence().1.unwrap();
        let (old_group, overflow) = Self::refill_group_from_sequence(
            &mut self.rng,
            base_group,
            elements,
            &base_group.min_splitter().clone(),
        );

        // it is very, really, extremely unlikely that an overflow happens here
        overflow.map(|seq_idx| self.handle_group_overflow(group_idx, seq_idx));
        let (splitters, sequences) = old_group.into_sequences();

        // now, move the remaining sequences to the next group
        let sequences = sequences.chain(big_sequence);
        let mut splitters = splitters.skip(n_skip).chain(big_splitter);
        // can not fail as one additional sequence has been inserted
        let small_splitter = splitters.next().unwrap();
        if group_idx + 1 == num_groups {
            // if the next group does not exist yet, initialize it with the available sequences
            self.r_distr.add_splitter(small_splitter.clone());
            let splitters: Vec<T> = splitters.collect();
            let base_group = BaseGroup::from_iter(_SCALING * max_seq_len, &splitters, sequences, small_splitter);
            self.group_list
                .push(Box::new(BufferedGroup::from_base_group(base_group)));
        } else {
            self.insert_sequences_to_group(
                group_idx + 1,
                small_splitter,
                splitters.collect::<Vec<_>>().into_iter().rev(),
                sequences.rev(),
            );
        }

        dbg_assertion!(self.structure_check());
    }

    /// Splits the sequence at the given index in two, returning the bigggest sequence
    /// of the group which is removed by the operation if the group is full.
    fn split_in_two(
        rng: &mut Rand,
        base_group: &mut BaseGroup<T>,
        seq_idx: usize,
    ) -> Option<(T, Sequence<T>)> {
        let small_seq = base_group.sequence_at(seq_idx);
        let mut big_seq = Sequence::new();
        let elements = mem::replace(small_seq, Sequence::new()).into_vec();
        let splitter = {
            let mut sample = Self::choose_sample(rng, &elements);
            sample.sort();
            sample[_SAMPLING / 2].clone()
        };

        for el in elements.into_iter() {
            match el.cmp(&splitter) {
                std::cmp::Ordering::Less => small_seq.push(el),
                std::cmp::Ordering::Equal => {
                    // tie breaking depending on sequence length, to avoid an all-elements-are-equal worst case
                    if small_seq.len() < big_seq.len() {
                        small_seq.push(el)
                    } else {
                        big_seq.push(el)
                    }
                }
                std::cmp::Ordering::Greater => big_seq.push(el),
            }
        }
        base_group.insert_sequence(splitter, big_seq, seq_idx + 1)
    }

    /// Replaces the group with a new one filled from the given sequence.
    /// If the new group overflows, returns the index of the overflowing sequence.
    fn refill_group_from_sequence(
        rng: &mut Rand,
        base_group: &mut BaseGroup<T>,
        seq: Sequence<T>,
        default: &T,
    ) -> (BaseGroup<T>, Option<usize>) {
        let max_seq_len = base_group.max_seq_len();
        if seq.len() == 0 {
            return (
                mem::replace(base_group, BaseGroup::empty(max_seq_len, default.clone())),
                None,
            );
        }

        let elements = seq.into_vec();
        let new_splitters: ArrayVec<[T; _K - 1]> = {
            // TODO: in theory, this could be replaced with an ArrayVec
            let mut sample: Vec<T> = Vec::new();
            for _ in 1.._K {
                sample.extend(Self::choose_sample(rng, &elements));
            }
            debug_assert!(sample.len() == (_K - 1) * _SAMPLING);
            sample.sort();
            sample
                .into_iter()
                .skip(_SAMPLING / 2)
                .step_by(_SAMPLING)
                .collect()
        };
        debug_assert!((new_splitters.len() == _K - 1));
        // TODO: set initial capacity of vecs to avoid unnecessary allocation
        let replaced = mem::replace(base_group, BaseGroup::new(max_seq_len, &new_splitters));
        base_group.forced_insert_all(&mut elements.into_iter());

        // let caller handle scanning?
        (replaced, base_group.scan_for_overflow(0))
    }

    fn scan_and_split(
        rng: &mut Rand,
        base_group: &mut BaseGroup<T>,
    ) -> Option<(
        impl DoubleEndedIterator<Item = T>,
        impl DoubleEndedIterator<Item = Sequence<T>>,
    )> {
        let mut splitters = Vec::new();
        let mut sequences = Vec::new();
        let mut curr_idx = 0;
        while let Some(seq_idx) = base_group.scan_for_overflow(curr_idx) {
            // don't use idx + 1, it could be necessary to split the sequence again
            curr_idx = seq_idx;
            Self::split_in_two(rng, base_group, seq_idx).map(|(splitter, seq)| {
                splitters.push(splitter);
                sequences.push(seq)
            });
        }
        dbg_assertion!(base_group.structure_check());

        if splitters.is_empty() {
            None
        } else {
            Some((splitters.into_iter(), sequences.into_iter()))
        }
    }

    /// If an error occurs, inserts the remaining elements and returns the index of the overflowing sequence.
    fn resolve_overflow<R, I: Iterator<Item = T>>(
        result: Result<R, GroupOverflowError<T, I>>,
    ) -> Option<usize> {
        result.err().map(
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

    fn choose_sample<'a>(rng: &mut Rand, elements: &'a [T]) -> ArrayVec<[T; _SAMPLING]> {
        debug_assert!(!elements.is_empty());
        let num_steps = elements.len() / _SAMPLING;
        let result: ArrayVec<[T; _SAMPLING]> = if num_steps == 0 {
            iter::repeat(elements)
                .flat_map(|els| els.iter().cloned())
                .take(_SAMPLING)
                .collect()
        } else {
            let step_idx = rng.gen_range(0, num_steps);
            let start = _SAMPLING * step_idx;
            elements[start..(start + _SAMPLING)]
                .iter()
                .cloned()
                .collect()
        };

        assert!(result.len() == _SAMPLING);
        result
    }

    // #[cfg(any(debug, test))]
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

    #[test]
    fn test_group_overflow() {
        let mut s_heap = SampleHeap::new();

        for i in 0..(_K * _M) {
            s_heap.push(i);
        }
        assert!(s_heap.groups.structure_check());

        let mut result = Vec::new();
        while let Some(el) = s_heap.pop() {
            result.push(el);
        }
        assert!(s_heap.is_empty());
        assert_eq!(result, (0..(_K * _M)).collect::<Vec<_>>());
    }

    #[test]
    fn test_group_overflow_reverse() {
        let mut s_heap = SampleHeap::new();

        for i in (0..(_K * _M)).rev() {
            s_heap.push(i);
        }
        assert!(s_heap.groups.structure_check());

        let mut result = Vec::new();
        while let Some(el) = s_heap.pop() {
            result.push(el);
        }
        assert!(s_heap.is_empty());
        assert_eq!(result, (0..(_K * _M)).collect::<Vec<_>>());
    }

    #[test]
    fn test_refill_edge_case() {
        let mut s_heap = SampleHeap::new();

        for _ in (0..(4 * _M)).rev() {
            s_heap.push(0);
        }
        assert!(s_heap.groups.structure_check());

        while let Some(_) = s_heap.pop() {}
        assert!(s_heap.is_empty());
    }
}
