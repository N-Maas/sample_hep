use crate::groups::*;
use crate::params::*;
use crate::primitives::*;
use smallvec::SmallVec;
use std::iter;

// TODO: implement Clone?
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
                let group = self.group_list[idx - 1].as_mut();
                let mapped = group.push(el).map_err(
                    |GroupOverflowError {
                         base_group,
                         seq_idx,
                         remaining,
                     }| {
                        base_group.forced_insert_all(remaining);
                        seq_idx
                    },
                );
                mapped.unwrap_or_else(|seq_idx| self.handle_group_overflow(idx, seq_idx))
            }
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
            let step = (_M + 1) as f64 / (_K + 1) as f64;
            let first = step.round() as usize;
            let splitter = elements[first].clone();
            self.r_distr.add_splitter(splitter);

            let splitters: Vec<T> = (2..=_K)
                .map(|i| elements[(i as f64 * step).round() as usize].clone())
                .collect();
            let mut base_group = BaseGroup::new(max_seq_len, &splitters);
            base_group.forced_insert_all(elements.drain(first..elements.len()));
            self.group_list
                .push(Box::new(BufferedGroup::from_base_group(base_group)));
        } else {
            let mid = elements.len() / 2;
            let seq = self.group_list.first_mut().unwrap().first_or_insert();
            for el in elements.drain((mid + 1)..elements.len()) {
                seq.push(el);
            }
            if seq.len() > max_seq_len {
                self.handle_group_overflow(0, 0);
            }

            let splitter = elements[mid].clone();
            debug_assert!(splitter <= *self.r_distr.splitter_at(0));
            self.r_distr.replace_splitter(splitter, 0);
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
