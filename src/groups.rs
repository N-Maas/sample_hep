use crate::params::*;
use crate::primitives::*;

use arrayvec::ArrayVec;
use std::{cmp::Reverse, collections::BinaryHeap, fmt::Debug, iter, mem};

/// contains the element that caused the overflow
pub(crate) struct HeapOverflowError<T>(T);
/// contains the index of the overflowing sequence and all elements that must be reinserted
pub(crate) struct GroupOverflowError<I: Iterator>(usize, I);

#[derive(Debug)]
pub(crate) struct BufferHeap<T: Ord> {
    // currently, we are building a min heap
    data: BinaryHeap<Reverse<T>>,
}

impl<T: Ord> BufferHeap<T> {
    pub fn new() -> Self {
        Self {
            data: BinaryHeap::with_capacity(_M),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    pub fn peek(&self) -> Option<&T> {
        self.data.peek().map(|el| &el.0)
    }

    pub fn pop(&mut self) -> Option<T> {
        self.data.pop().map(|el| el.0)
    }

    pub fn push(&mut self, el: T) -> Result<(), HeapOverflowError<T>> {
        debug_assert!(self.data.len() <= _M);
        if self.data.len() == _M {
            Err(HeapOverflowError(el))
        } else {
            self.data.push(Reverse(el));
            Ok(())
        }
    }

    pub fn extract_elements(&mut self) -> Vec<T> {
        // TODO unnecessary copying
        self.data.drain().map(|el| el.0).collect()
    }

    /// used for checking invariants
    pub fn min(&self) -> Option<&T> {
        self.data.iter().min().map(|el| &el.0)
    }

    /// used for checking invariants
    pub fn max(&self) -> Option<&T> {
        self.data.iter().max().map(|el| &el.0)
    }
}

#[derive(Debug)]
pub(crate) struct BaseGroup<T: Ord> {
    distr: KDistribute<T>,
    // TODO: better without deallocation of sequences?!
    // the sequences are arranged in reverse order, so the first one can be removed without overhead
    sequences: ArrayVec<[Sequence<T>; _K]>,
    // maximum allowed length of a sequence for this group
    max_seq_len: usize,
}

impl<T: Ord> BaseGroup<T> {
    pub fn is_empty(&self) -> bool {
        self.sequences.is_empty()
    }

    // pub fn max_seq_len(&self) -> usize {
    //     self.max_seq_len
    // }

    pub fn sequence_at(&mut self, idx: usize) -> &mut Sequence<T> {
        let rev_idx = Self::rev_idx(&self.sequences, idx);
        &mut self.sequences[rev_idx]
    }

    /// does not test size limit of the sequences
    pub fn forced_insert_all(&mut self, iter: impl Iterator<Item = T>) {
        for el in iter {
            let idx = self.distr.distribute(&el);
            unsafe { Self::sequence_at_unchecked(&mut self.sequences, idx).push(el) }
        }
    }

    pub fn overflowing_insert_all(
        &mut self,
        mut iter: impl Iterator<Item = T>,
    ) -> Result<(), GroupOverflowError<impl Iterator<Item = T>>> {
        for el in &mut iter {
            let idx = self.distr.distribute(&el);
            let sequence = unsafe { Self::sequence_at_unchecked(&mut self.sequences, idx) };
            if sequence.len() < self.max_seq_len {
                sequence.push(el);
            } else {
                return Err(GroupOverflowError(idx, iter.chain(iter::once(el))));
            }
        }
        Ok(())
    }

    // TODO: replace sequence (?)

    /// Inserts a sequence at the given index by specifying the next smaller splitter.
    /// If the number of sequences is full, the largest is removed and returned with the according splitter.
    /// Insertion to first position is not possible.
    pub fn insert_sequence(
        &mut self,
        splitter: T,
        seq: Sequence<T>,
        idx: usize,
    ) -> Option<(T, Sequence<T>)> {
        debug_assert!(idx < _K);
        debug_assert!(splitter <= *self.distr.splitter_at(idx - 1));
        let rev_idx = Self::rev_idx(&self.sequences, idx);

        let result = if !self.sequences.is_full() {
            debug_assert!(rev_idx < self.sequences.len(), "idx={:?}", idx);
            self.sequences.insert(rev_idx, seq);
            self.distr.insert_splitter(splitter);
            None
        } else {
            debug_assert!(idx > 0);
            let larger_range = &mut self.sequences[0..=rev_idx];
            larger_range.rotate_left(1);
            Some((
                self.distr.insert_splitter(splitter),
                mem::replace(&mut larger_range[rev_idx], seq),
            ))
        };

        debug_assert!(self.structure_check());
        result
    }

    unsafe fn sequence_at_unchecked(
        sequences: &mut ArrayVec<[Sequence<T>; _K]>,
        idx: usize,
    ) -> &mut Sequence<T> {
        // case distinction is currently necessary if group is not full
        let rev_idx = Self::rev_idx(sequences, idx);
        debug_assert!(rev_idx < sequences.len(), "rev_idx={:?}", rev_idx);
        sequences.get_unchecked_mut(rev_idx)
    }

    // TODO: the index scheme is a bit broken currently
    fn rev_idx(sequences: &ArrayVec<[Sequence<T>; _K]>, idx: usize) -> usize {
        if idx == 0 {
            sequences.len() - 1
        } else {
            _K - idx - 1
        }
    }

    /// used for checking invariants
    pub fn structure_check(&self) -> bool {
        let idx_delta = _K - self.sequences.len();
        self.distr.structure_check()
            && self
                .sequences
                .iter()
                .skip(1)
                .rev()
                .enumerate()
                .all(|(i, s)| s.max().unwrap() <= self.distr.splitter_at(i + idx_delta))
            && self
                .sequences
                .iter()
                .rev()
                .skip(1)
                .enumerate()
                .all(|(i, s)| s.min().unwrap() >= self.distr.splitter_at(i + idx_delta))
            && self.sequences.iter().all(|s| s.len() <= self.max_seq_len)
    }

    /// used for checking invariants
    pub fn min(&self) -> Option<&T> {
        self.sequences.last().map(|s| s.min().unwrap())
    }

    /// used for checking invariants
    pub fn max(&self) -> Option<&T> {
        self.sequences.first().map(|s| s.max().unwrap())
    }
}

impl<T: Ord + Clone> BaseGroup<T> {
    /// adds a new smallest sequence and splitter if the groups number of sequences is not full
    pub fn push_sequence(&mut self, splitter: T, seq: Sequence<T>) {
        debug_assert!(self.sequences.len() < _K);
        debug_assert!(
            self.sequences.len() <= 1
                || splitter <= *self.distr.splitter_at(_K - self.sequences.len())
        );
        self.sequences.push(seq);
        for i in 0..(_K - self.sequences.len()) {
            self.distr.replace_splitter(splitter.clone(), i);
        }
        debug_assert!(self.structure_check());
    }

    pub fn pop_sequence(&mut self) -> Option<Sequence<T>> {
        let result = self.sequences.pop();

        // necessary to ensure a valid structure of the splitters:
        // minimal elements are distributed to either index 0 or the minimal sequence
        // 0 is correctly adjusted by the rev_idx function
        if !self.sequences.is_empty() {
            let min = self.distr.splitter_at(0);
            self.distr.replace_splitter(min.clone(), _K - self.sequences.len() - 1);
        }
        debug_assert!(self.structure_check());
        result
    }
}

#[derive(Debug)]
pub(crate) struct BufferedGroup<T: Ord> {
    base: BaseGroup<T>,
    buffer: GroupBuffer<T>,
}

impl<T: Ord> BufferedGroup<T> {
    pub fn is_empty(&self) -> bool {
        self.base.is_empty() && self.buffer.is_empty()
    }

    // pub fn max_seq_len(&self) -> usize {
    //     self.max_seq_len
    // }

    pub fn push<'a>(
        &'a mut self,
        el: T,
    ) -> Result<(), GroupOverflowError<impl Iterator<Item = T> + 'a>> {
        if !self.buffer.is_full() {
            self.buffer.push(el);
            Ok(())
        } else {
            self.base.overflowing_insert_all(self.buffer.drain())
        }
    }

    pub fn clear_buffer<'a>(
        &'a mut self,
    ) -> Result<&'a mut BaseGroup<T>, GroupOverflowError<impl Iterator<Item = T> + 'a>> {
        let base = &mut self.base;
        base.overflowing_insert_all(self.buffer.drain())
            .map(|_| base)
    }

    /// may exceed the size limits of the sequences
    pub fn clear_buffer_forced(&mut self) -> &mut BaseGroup<T> {
        self.base.forced_insert_all(self.buffer.drain());
        &mut self.base
    }

    /// used for checking invariants
    pub fn structure_check(&self) -> bool {
        self.base.structure_check()
    }

    /// used for checking invariants
    pub fn min(&self) -> Option<&T> {
        self.base.min().into_iter().chain(self.buffer.min()).min()
    }

    /// used for checking invariants
    pub fn max(&self) -> Option<&T> {
        self.base.max().into_iter().chain(self.buffer.max()).max()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::iter::FromIterator;

    #[test]
    fn base_group_basic() {
        let mut s1 = Sequence::new();
        s1.push(1);
        let mut s2 = Sequence::new();
        s2.push(4);
        let splitters = [2; _K - 1];

        let mut group = BaseGroup {
            distr: KDistribute::new(&splitters),
            sequences: ArrayVec::from_iter(vec![s2, s1]),
            max_seq_len: 2,
        };
        assert!(!group.is_empty());
        assert!(group.structure_check());

        group.forced_insert_all(vec![0, 2].into_iter());
        assert!(group.structure_check());
        assert_eq!(*group.min().unwrap(), 0);
        assert_eq!(*group.max().unwrap(), 4);

        let res = group.overflowing_insert_all(vec![0, 1].into_iter());
        match res {
            Ok(()) => assert!(false),
            Err(GroupOverflowError(i, iter)) => {
                let mut remaining = iter.collect::<Vec<i32>>();
                remaining.sort();
                assert_eq!(*group.sequence_at(i).min().unwrap(), 0);
                assert_eq!(remaining, vec![0, 1]);
            }
        }

        let res = group.overflowing_insert_all(vec![8, 9].into_iter());
        match res {
            Ok(()) => assert!(false),
            Err(GroupOverflowError(i, iter)) => {
                let mut remaining = iter.collect::<Vec<i32>>();
                remaining.sort();
                assert_eq!(*group.sequence_at(i).min().unwrap(), 2);
                assert_eq!(remaining, vec![8, 9]);
            }
        }
    }

    #[test]
    fn base_group_seqs() {
        let splitters = [2 * _K; _K - 1];
        let mut group = BaseGroup {
            distr: KDistribute::new(&splitters),
            sequences: ArrayVec::new(),
            max_seq_len: 1,
        };
        assert!(group.structure_check());
        assert_eq!(None, group.min());
        assert_eq!(None, group.max());

        for i in (0.._K).rev() {
            let mut seq = Sequence::new();
            seq.push(2 * i);
            group.push_sequence(2 * i, seq);
        }
        assert_eq!(*group.min().unwrap(), 0);
        assert_eq!(*group.max().unwrap(), 2 * _K - 2);

        let mut seq = Sequence::new();
        seq.push(2 * _K - 3);
        let (val, _) = group.insert_sequence(2 * _K - 3, seq, _K - 1).unwrap();
        assert_eq!(val, 2 * _K - 2);
        assert_eq!(*group.max().unwrap(), 2 * _K - 3);

        let mut seq = Sequence::new();
        seq.push(2);
        let (val, _) = group.insert_sequence(2, seq, 1).unwrap();
        assert_eq!(val, 2 * _K - 3);
        assert_eq!(*group.max().unwrap(), 2 * _K - 4);
    }

    #[test]
    fn base_group_insert_elements() {
        let splitters = [0; _K - 1];
        let mut group = BaseGroup {
            distr: KDistribute::new(&splitters),
            sequences: ArrayVec::new(),
            max_seq_len: 5,
        };
        assert!(group.structure_check());

        for i in (1..=3).rev() {
            let mut seq = Sequence::new();
            seq.push(2 * i);
            group.push_sequence(2 * i, seq);
        }

        group.forced_insert_all(vec![1,3,5,7].into_iter());
        assert_eq!(*group.min().unwrap(), 1);
        assert_eq!(*group.max().unwrap(), 7);

        let mut smallest: Vec<i32> = group.pop_sequence().unwrap().drain().collect();
        smallest.sort();
        assert_eq!(vec![1,2,3], smallest);

        group.forced_insert_all(vec![1,5].into_iter());
        let mut smallest: Vec<i32> = group.pop_sequence().unwrap().drain().collect();
        smallest.sort();
        assert_eq!(vec![1,4,5,5], smallest);

        group.forced_insert_all(vec![3,5,7].into_iter());
        let mut smallest: Vec<i32> = group.pop_sequence().unwrap().drain().collect();
        smallest.sort();
        assert_eq!(vec![3,5,6,7,7], smallest);
    }
}
