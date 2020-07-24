use crate::params::*;
use crate::primitives::*;

use arrayvec::ArrayVec;
use std::{cmp::Reverse, collections::BinaryHeap, iter};

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

    // TODO: insert & replace sequence, drain smallest sequence

    /// used for checking invariants
    pub fn structure_check(&self) -> bool {
        self.sequences
            .iter()
            .skip(1)
            .rev()
            .enumerate()
            .all(|(i, s)| s.max().unwrap() < self.distr.splitter_at(i))
            && self
                .sequences
                .iter()
                .rev()
                .skip(1)
                .enumerate()
                .all(|(i, s)| s.min().unwrap() >= self.distr.splitter_at(i))
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
}
