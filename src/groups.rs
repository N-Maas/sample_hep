use crate::params::*;
use crate::primitives::*;

use arrayvec::ArrayVec;
use std::{cmp::Reverse, collections::BinaryHeap};

pub(crate) struct HeapOverflowError<T>(T);
pub(crate) struct GroupOverflowError<T>(usize, T);

pub(crate) struct BufferHeap<T: Ord> {
    // currently, we are building a min heap
    data: BinaryHeap<Reverse<T>>,
}

impl<T: Ord> BufferHeap<T> {
    pub(crate) fn new() -> Self {
        Self {
            data: BinaryHeap::with_capacity(_M),
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    pub(crate) fn peek(&self) -> Option<&T> {
        self.data.peek().map(|el| &el.0)
    }

    pub(crate) fn pop(&mut self) -> Option<T> {
        self.data.pop().map(|el| el.0)
    }

    pub(crate) fn push(&mut self, el: T) -> Result<(), HeapOverflowError<T>> {
        debug_assert!(self.data.len() <= _M);
        if self.data.len() == _M {
            Err(HeapOverflowError(el))
        } else {
            self.data.push(Reverse(el));
            Ok(())
        }
    }
}

pub(crate) struct Group<T: Ord> {
    // TODO: ugly
    pub(crate) distr: KDistribute<T>,
    buffer: GroupBuffer<T>,
    // TODO: better without deallocation of sequences?!
    sequences: ArrayVec<[Sequence<T>; _K]>,
    max_seq_len: usize,
}

impl<T: Ord> Group<T> {
    pub(crate) fn is_empty(&self) -> bool {
        self.sequences.is_empty() && self.buffer.is_empty()
    }

    pub(crate) fn max_seq_len(&self) -> usize {
        self.max_seq_len
    }

    pub(crate) fn sequence_at(&mut self, idx: usize) -> &mut Sequence<T> {
        let rev_idx = _K - idx - 1;
        &mut self.sequences[rev_idx]
    }

    unsafe fn sequence_at_unchecked(sequences: &mut ArrayVec<[Sequence<T>; _K]>, idx: usize) -> &mut Sequence<T> {
        let rev_idx = _K - idx - 1;
        debug_assert!(rev_idx < sequences.len());
        sequences.get_unchecked_mut(rev_idx)
    }

    /// may exceed the size limits of the sequences
    pub(crate) fn clear_buffer(&mut self) {
        let distr = &self.distr;
        let seqs = &mut self.sequences;
        self.buffer.drain().for_each(|el| {
            let idx = distr.distribute(&el);
            unsafe { Self::sequence_at_unchecked(seqs, idx).push(el) }
        });
    }

    /// skips buffer and and does not test size limit of the sequences
    pub(crate) fn forced_append(&mut self, iter: impl Iterator<Item=T>) {
        for el in iter {
            let idx = self.distr.distribute(&el);
            unsafe { Self::sequence_at_unchecked(&mut self.sequences, idx).push(el) }
        }
    }

    pub(crate) fn structure_check(&self) -> bool {
        todo!()
    }

    // TODO: insert & replace sequence
}
