use crate::{dbg_assertion, params::*, primitives::*};

use arrayvec::ArrayVec;
use std::{cmp::Reverse, collections::BinaryHeap, fmt::Debug, iter, mem, mem::MaybeUninit};

/// contains the element that caused the overflow
#[derive(Debug)]
pub(crate) struct HeapOverflowError<T>(pub T);
/// contains the index of the overflowing sequence and all elements that must be reinserted
#[derive(Debug)]
pub(crate) struct GroupOverflowError<'a, T: Ord, I: Iterator<Item = T>> {
    pub base_group: &'a mut BaseGroup<T>,
    pub seq_idx: usize,
    pub remaining: I,
}

impl<'a, T: Ord, I: Iterator<Item = T>> GroupOverflowError<'a, T, I> {
    fn append_remaining(
        self,
        iter: impl Iterator<Item = T>,
    ) -> GroupOverflowError<'a, T, impl Iterator<Item = T>> {
        GroupOverflowError {
            base_group: self.base_group,
            seq_idx: self.seq_idx,
            remaining: self.remaining.chain(iter),
        }
    }
}

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

    pub fn drain<'a>(&'a mut self) -> impl Iterator<Item = T> + 'a {
        // TODO unnecessary copying when emptying deletion heap?
        self.data.drain().map(|el| el.0)
    }

    // // #[cfg(any(debug, test))]
    // pub fn min(&self) -> Option<&T> {
    //     self.data.iter().min().map(|el| &el.0)
    // }

    // #[cfg(any(debug, test))]
    pub fn max(&self) -> Option<&T> {
        self.data.iter().max().map(|el| &el.0)
    }
}

#[derive(Debug)]
pub(crate) struct BaseGroup<T: Ord> {
    distr: KDistribute<T>,
    // the sequences are pushed and popped to the front, i.e. the last self.num_sequences are active.
    sequences: [Sequence<T>; _K],
    // number of active sequences
    num_sequences: usize,
    // maximum allowed length of a sequence for this group
    max_seq_len: usize,
}

impl<T: Ord> BaseGroup<T> {
    pub fn is_empty(&self) -> bool {
        self.sequences[_K - self.num_sequences.._K]
            .iter()
            .all(|seq| seq.len() == 0)
    }

    pub fn num_sequences(&self) -> usize {
        self.num_sequences
    }

    pub fn max_seq_len(&self) -> usize {
        self.max_seq_len
    }

    pub fn sequence_at(&mut self, idx: usize) -> &mut Sequence<T> {
        debug_assert!(idx >= _K - self.num_sequences && idx < _K);
        &mut self.sequences[idx]
    }

    /// does not test size limit of the sequences
    pub fn forced_insert_all(&mut self, iter: impl Iterator<Item = T>) {
        if self.num_sequences == 0 {
            self.num_sequences += 1;
        }

        for el in iter {
            let idx = self.distribute(&el);
            unsafe {
                debug_assert!(idx >= _K - self.num_sequences && idx < _K);
                self.sequences.get_unchecked_mut(idx)
            }
            .push(el);
        }
    }

    pub fn overflowing_insert_all(
        &mut self,
        mut iter: &mut impl Iterator<Item = T>,
    ) -> Result<&mut Self, GroupOverflowError<T, iter::Once<T>>> {
        if self.num_sequences == 0 {
            self.num_sequences += 1;
        }

        for el in &mut iter {
            let idx = self.distribute(&el);
            let sequence = unsafe {
                debug_assert!(idx >= _K - self.num_sequences && idx < _K);
                self.sequences.get_unchecked_mut(idx)
            };
            if sequence.len() < self.max_seq_len {
                sequence.push(el);
            } else {
                return Err(GroupOverflowError {
                    base_group: self,
                    seq_idx: idx,
                    remaining: iter::once(el),
                });
            }
        }
        Ok(self)
    }

    pub fn min_splitter(&self) -> &T {
        self.distr.splitter_at(0)
    }

    fn distribute(&self, el: &T) -> usize {
        let idx = self.distr.distribute(&el);
        // TODO: the index scheme is a bit broken currently
        if idx == 0 {
            _K - self.num_sequences
        } else {
            idx
        }
    }

    // should we require that sequences are non-empty?
    // -> probably not
    // #[cfg(any(debug, test))]
    /// - does not check sequence sizes
    pub fn base_structure_check(&self) -> bool {
        let mut valid = self.distr.structure_check();
        let mut prev_max = self.sequences.first().map(|s| s.max()).flatten();
        for (i, seq) in self.sequences.iter().skip(1).enumerate() {
            let splitter = self.distr.splitter_at(i);
            valid &= (i + 1 >= _K - self.num_sequences) || seq.len() == 0;
            valid &= prev_max.map_or(true, |m| m <= splitter);
            valid &=
                (i + 1 <= _K - self.num_sequences) || seq.min().map_or(true, |m| splitter <= m);
            prev_max = seq.max()
        }
        valid
    }

    // #[cfg(any(debug, test))]
    pub fn structure_check(&self) -> bool {
        self.base_structure_check() && self.sequences.iter().all(|s| s.len() <= self.max_seq_len)
    }

    // #[cfg(any(debug, test))]
    pub fn min(&self) -> Option<&T> {
        self.sequences
            .get(_K - self.num_sequences)
            .map(|s| s.min())
            .flatten()
    }

    // #[cfg(any(debug, test))]
    pub fn max(&self) -> Option<&T> {
        self.sequences.last().map(|s| s.max()).flatten()
    }
}

impl<T: Ord + Clone> BaseGroup<T> {
    pub fn replace_splitters(&mut self, splitters: &[T]) {
        debug_assert!(self.is_empty());
        self.distr = KDistribute::new(splitters);
        self.num_sequences = splitters.len() + 1;
    }

    /// Adds a new smallest sequence and splitter if the groups number of sequences is not full.
    /// The specified splitter must be bigger then the sequence.
    /// To ensure consistency, a smaller default splitter is used.
    pub fn push_sequence(&mut self, splitter: T, seq: Sequence<T>, default: T) {
        debug_assert!(self.num_sequences < _K);
        debug_assert!(
            self.num_sequences <= 1 || splitter <= *self.distr.splitter_at(_K - self.num_sequences)
        );
        for i in 0..usize::min(_K - self.num_sequences - 1, _K - 1) {
            self.distr.replace_splitter(default.clone(), i);
        }
        if !(self.num_sequences == 0) {
            self.distr
                .replace_splitter(splitter, _K - self.num_sequences - 1);
        }
        self.sequences[_K - self.num_sequences - 1] = seq;
        self.num_sequences += 1;
        dbg_assertion!(self.base_structure_check());
    }

    /// Returns a bigger splitter, if available.
    pub fn pop_sequence(&mut self) -> (Option<T>, Option<&mut Sequence<T>>) {
        self.pop_sequence_if(|_| true)
    }

    /// Returns a bigger splitter, if available.
    pub fn pop_sequence_if(
        &mut self,
        predicate: impl FnOnce(&Sequence<T>) -> bool,
    ) -> (Option<T>, Option<&mut Sequence<T>>) {
        if self.num_sequences > 0 && predicate(&self.sequences[_K - self.num_sequences]) {
            self.num_sequences -= 1;
            let seq = &mut self.sequences[_K - self.num_sequences - 1];

            // necessary to ensure a valid structure of the splitters:
            // minimal elements are distributed to either index 0 or the minimal sequence
            // 0 is correctly adjusted by the rev_idx function
            if self.num_sequences > 0 {
                let smaller_splitter = self.distr.splitter_at(0).clone();
                let splitter = self
                    .distr
                    .replace_splitter(smaller_splitter, _K - self.num_sequences - 1);
                (Some(splitter), Some(seq))
            } else {
                (None, Some(seq))
            }
        } else {
            (None, None)
        }
    }

    /// Pop all empty sequences.
    pub fn pop_empty(&mut self) {
        while let (_, Some(_)) = self.pop_sequence_if(|s| s.len() == 0) {}
    }

    /// Inserts a sequence before the sequence that is currently at the given index.
    /// The next smaller splitter is specified.
    /// If the number of sequences is full, the largest is removed and returned with the according splitter.
    /// Insertion to first position is not possible (as the splitter would be invalid).
    pub fn insert_sequence(
        &mut self,
        splitter: T,
        seq: Sequence<T>,
        idx: usize,
    ) -> Option<(T, Sequence<T>)> {
        debug_assert!(idx > (_K - self.num_sequences) && idx <= _K);
        debug_assert!(idx == _K || splitter <= *self.distr.splitter_at(idx - 1));

        let result = if self.num_sequences < _K {
            // really nasty edge case for invalid splitters
            if idx == _K - self.num_sequences + 1 {
                for i in 0..(idx - 1) {
                    self.distr.replace_splitter(splitter.clone(), i);
                }
            } else {
                self.distr.insert_splitter_at(splitter, idx - 2, true);
            }
            let smaller_range = &mut self.sequences[(_K - self.num_sequences - 1)..idx];
            smaller_range.rotate_left(1);
            self.sequences[idx - 1] = seq;
            self.num_sequences += 1;
            None
        } else if idx == _K {
            Some((splitter, seq))
        } else {
            let larger_range = &mut self.sequences[idx.._K];
            larger_range.rotate_right(1);
            Some((
                self.distr.insert_splitter_at(splitter, idx - 1, false),
                mem::replace(&mut larger_range[0], seq),
            ))
        };

        dbg_assertion!(self.base_structure_check());
        result
    }

    pub fn scan_for_overflow(&self, start_idx: usize) -> Option<usize> {
        let n_empty = _K - self.num_sequences;
        let n_skip = n_empty + start_idx;
        let result = self
            .sequences
            .iter()
            .skip(n_skip)
            .enumerate()
            .find(|(_, seq)| seq.len() > self.max_seq_len)
            .map(|(i, _)| n_skip + i);

        debug_assert!(result.map_or(true, |i| self.sequences[i].len() > self.max_seq_len));
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

    pub fn num_sequences(&self) -> usize {
        self.base.num_sequences()
    }

    pub fn max_seq_len(&self) -> usize {
        self.base.max_seq_len()
    }

    // TODO: rework to scanning afterwards for avoiding size checks?
    pub fn push<'a>(
        &'a mut self,
        el: T,
    ) -> Result<(), GroupOverflowError<T, impl Iterator<Item = T> + 'a>> {
        if !self.buffer.is_full() {
            self.buffer.push(el);
            Ok(())
        } else {
            let mut iter = self.buffer.drain().chain(iter::once(el));
            self.base
                .overflowing_insert_all(&mut iter)
                .map_err(|e| e.append_remaining(iter))
                .map(|_| ())
        }
    }

    pub fn clear_buffer<'a>(
        &'a mut self,
    ) -> Result<&'a mut BaseGroup<T>, GroupOverflowError<T, impl Iterator<Item = T> + 'a>> {
        let mut iter = self.buffer.drain();
        self.base
            .overflowing_insert_all(&mut iter)
            .map_err(|e| e.append_remaining(iter))
    }

    /// may exceed the size limits of the sequences
    pub fn clear_buffer_forced(&mut self) -> &mut BaseGroup<T> {
        self.base.forced_insert_all(self.buffer.drain());
        &mut self.base
    }

    /// only usable if buffer is empty
    pub fn base_group(&mut self) -> &mut BaseGroup<T> {
        debug_assert!(self.buffer.is_empty());
        &mut self.base
    }

    pub fn first_or_insert(&mut self) -> &mut Sequence<T> {
        if self.base.num_sequences == 0 {
            self.base.num_sequences += 1;
        }
        &mut self.base.sequences[_K - self.base.num_sequences]
    }

    // #[cfg(any(debug, test))]
    pub fn structure_check(&self) -> bool {
        self.base.structure_check()
    }

    // #[cfg(any(debug, test))]
    pub fn min(&self) -> Option<&T> {
        self.base.min().into_iter().chain(self.buffer.min()).min()
    }

    // #[cfg(any(debug, test))]
    pub fn max(&self) -> Option<&T> {
        self.base.max().into_iter().chain(self.buffer.max()).max()
    }
}

impl<'a, T: Ord + Clone + 'a> BufferedGroup<T> {
    // TODO: better solution for KDistribute consistency requirements?
    /// Adds a new smallest sequence and splitter if the groups number of sequences is not full.
    /// The specified splitter must be bigger then the sequence.
    /// To ensure consistency, a smaller default splitter is used.
    pub fn push_sequence(&mut self, splitter: T, seq: Sequence<T>, default: T) {
        self.base.push_sequence(splitter, seq, default);
    }

    /// Destructures into the sequences and splitters. Note that invalid splitters are returned, too.
    pub fn into_sequences(
        self,
    ) -> (
        impl Iterator<Item = T> + 'a,
        impl DoubleEndedIterator<Item = Sequence<T>> + 'a,
    ) {
        debug_assert!(self.buffer.is_empty());
        (
            self.base.distr.into_iter(),
            ArrayVec::<[Sequence<T>; _K]>::from(self.base.sequences)
                .into_iter()
                .skip(_K - self.base.num_sequences),
        )
    }
}

// structs that provide an API for efficiently initializing groups without unnecessary copies
pub(crate) enum GroupBuilder<'a, T: Ord> {
    Borrowed(&'a mut BufferedGroup<T>),
    Uninit(Box<MaybeUninit<BufferedGroup<T>>>),
}
pub(crate) enum GroupInit<'a, T: Ord> {
    Borrowed(&'a mut BufferedGroup<T>),
    Init(Box<BufferedGroup<T>>),
}

impl<'a, T: Ord> GroupBuilder<'a, T> {
    // requires unstable feature, but avoids unecessary copying
    pub fn new() -> GroupBuilder<'a, T>
    where
        T: 'a,
    {
        // we need to zero the memory, because uninitialized padding seems to be UB (at least, segfaults appear without zeroing)
        GroupBuilder::<'a, T>::Uninit(Box::new_zeroed())
    }

    pub fn borrowed(group: &'a mut BufferedGroup<T>) -> Self {
        debug_assert!(group.is_empty());
        Self::Borrowed(group)
    }
}

impl<'a, T: Ord + Clone> GroupBuilder<'a, T> {
    pub fn init_empty(self, max_seq_len: usize, default: T) -> GroupInit<'a, T> {
        self.init(&[default], 0, max_seq_len, iter::empty())
    }

    pub fn init_from_splitters(self, max_seq_len: usize, splitters: &[T]) -> GroupInit<'a, T> {
        self.init(splitters, splitters.len() + 1, max_seq_len, iter::empty())
    }

    pub fn init_from_iter(
        self,
        max_seq_len: usize,
        splitters: &[T],
        iter: impl DoubleEndedIterator<Item = Sequence<T>>,
        default: T,
    ) -> GroupInit<'a, T> {
        let num_sequences = splitters.len() + 1;
        let default = &[default];
        let splitters = if !splitters.is_empty() {
            splitters
        } else {
            default
        };
        self.init(splitters, num_sequences, max_seq_len, iter)
    }

    pub fn init(
        self,
        splitters: &[T],
        num_sequences: usize,
        max_seq_len: usize,
        iter: impl DoubleEndedIterator<Item = Sequence<T>>,
    ) -> GroupInit<'a, T> {
        match self {
            GroupBuilder::Borrowed(group) => {
                let bg = group.base_group();
                bg.distr = KDistribute::new(splitters);
                bg.num_sequences = num_sequences;
                bg.max_seq_len = max_seq_len;
                for (i, el) in iter.rev().enumerate() {
                    bg.sequences[_K - i - 1] = el;
                }
                GroupInit::Borrowed(group)
            }
            GroupBuilder::Uninit(mut group) => {
                Self::init_unsafe(group.as_mut(), splitters, num_sequences, max_seq_len);
                Self::init_sequences(group.as_mut(), iter);
                GroupInit::Init(unsafe { group.assume_init() })
            }
        }
    }

    fn init_unsafe(
        group: &mut MaybeUninit<BufferedGroup<T>>,
        splitters: &[T],
        num_sequences: usize,
        max_seq_len: usize,
    ) {
        unsafe {
            let base_group: *mut BaseGroup<T> = &mut (*group.as_mut_ptr()).base as *mut _;
            (*group.as_mut_ptr()).buffer = GroupBuffer::new();
            (*base_group).distr = KDistribute::new(splitters);
            (*base_group).num_sequences = num_sequences;
            (*base_group).max_seq_len = max_seq_len;
        }
    }

    fn init_sequences(
        group: &mut MaybeUninit<BufferedGroup<T>>,
        iter: impl DoubleEndedIterator<Item = Sequence<T>>,
    ) {
        let seqs: *mut [Sequence<T>; _K] =
            unsafe { &mut (*group.as_mut_ptr()).base.sequences as *mut _ };
        let mut idx = _K;
        for (i, el) in iter.rev().enumerate() {
            idx = _K - i - 1;
            unsafe { (*seqs)[idx] = el };
        }
        for i in (0..idx).rev() {
            unsafe { (*seqs)[i] = Sequence::new() };
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn empty_group<T: Ord + Clone + 'static>(max_seq_len: usize, default: T) -> BaseGroup<T> {
        match GroupBuilder::new().init_empty(max_seq_len, default) {
            GroupInit::Borrowed(_) => panic!(),
            GroupInit::Init(group) => group.base,
        }
    }

    #[test]
    fn base_group_basic() {
        let mut s1 = Sequence::new();
        s1.push(1);
        let mut s2 = Sequence::new();
        s2.push(4);
        let splitters = [2; 1];

        let mut group =
            match GroupBuilder::new().init_from_iter(2, &splitters, vec![s1, s2].into_iter(), 0) {
                GroupInit::Borrowed(_) => panic!(),
                GroupInit::Init(group) => group.base,
            };
        assert!(!group.is_empty());
        assert!(group.structure_check());

        group.forced_insert_all(vec![0, 2].into_iter());
        assert!(group.structure_check());
        assert_eq!(*group.min().unwrap(), 0);
        assert_eq!(*group.max().unwrap(), 4);

        let res = group.overflowing_insert_all(&mut vec![0].into_iter());
        match res {
            Ok(_) => assert!(false),
            Err(e) => {
                assert_eq!(*e.base_group.sequence_at(e.seq_idx).min().unwrap(), 0);
                assert_eq!(e.remaining.last(), Some(0));
            }
        }

        let res = group.overflowing_insert_all(&mut vec![8].into_iter());
        match res {
            Ok(_) => assert!(false),
            Err(e) => {
                assert_eq!(*e.base_group.sequence_at(e.seq_idx).min().unwrap(), 2);
                assert_eq!(e.remaining.last(), Some(8));
            }
        }
    }

    #[test]
    fn base_group_empty() {
        let mut group = empty_group(4, 0);
        group.forced_insert_all(iter::once(0));
        assert!(group.structure_check());
    }

    #[test]
    fn base_group_seqs() {
        let mut group = empty_group(1, 2 * _K);
        assert!(group.structure_check());
        assert_eq!(None, group.min());
        assert_eq!(None, group.max());

        for i in (0.._K).rev().step_by(2) {
            let mut seq = Sequence::new();
            seq.push(2 * i - 2);
            group.push_sequence(2 * i + 2, seq, 2 * i + 2);
            let mut seq = Sequence::new();
            seq.push(2 * i);
            group.insert_sequence(2 * i, seq, i + 1);
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

        let (splits, seqs) = BufferedGroup {
            base: group,
            buffer: GroupBuffer::new(),
        }
        .into_sequences();
        assert_eq!(_K, seqs.count());
        assert_eq!(_K - 1, splits.count());
    }

    #[test]
    fn base_group_insert_elements() {
        let mut group = empty_group(3, 0);
        assert!(group.structure_check());

        for i in (1..=3).rev() {
            let mut seq = Sequence::new();
            seq.push(2 * i);
            group.push_sequence(2 * i + 2, seq, 0);
        }

        group.forced_insert_all(vec![1, 3, 5, 7].into_iter());
        assert_eq!(*group.min().unwrap(), 1);
        assert_eq!(*group.max().unwrap(), 7);

        let mut smallest: Vec<i32> = group.pop_sequence().1.unwrap().drain().collect();
        smallest.sort();
        assert_eq!(vec![1, 2, 3], smallest);

        group.forced_insert_all(vec![1, 5].into_iter());
        let mut smallest: Vec<i32> = group.pop_sequence().1.unwrap().drain().collect();
        smallest.sort();
        assert_eq!(vec![1, 4, 5, 5], smallest);

        group.forced_insert_all(vec![3, 5, 7].into_iter());
        let overflow = group.scan_for_overflow(0);
        assert_eq!(overflow, Some(_K - 1));

        let mut smallest: Vec<i32> = group.pop_sequence().1.unwrap().drain().collect();
        smallest.sort();
        assert_eq!(vec![3, 5, 6, 7, 7], smallest);
    }

    #[test]
    fn base_group_from_iter() {
        let mut seq1 = Sequence::new();
        seq1.push(0);
        let mut seq2 = Sequence::new();
        seq2.push(2);
        let mut seq3 = Sequence::new();
        seq3.push(4);

        let splitters = [];
        let mut group =
            match GroupBuilder::new().init_from_iter(2, &splitters, vec![seq1].into_iter(), 0) {
                GroupInit::Borrowed(_) => panic!(),
                GroupInit::Init(group) => group.base,
            };
        assert!(group.structure_check());

        assert!(group.insert_sequence(4, seq3, _K).is_none());
        assert!(group.insert_sequence(2, seq2, _K - 1).is_none());

        group.forced_insert_all(vec![1, 3].into_iter());

        let mut smallest: Vec<i32> = group.pop_sequence().1.unwrap().drain().collect();
        smallest.sort();
        assert_eq!(vec![0, 1], smallest);

        let mut smallest: Vec<i32> = group.pop_sequence().1.unwrap().drain().collect();
        smallest.sort();
        assert_eq!(vec![2, 3], smallest);
    }

    #[test]
    fn buffered_group() {
        use std::iter::FromIterator;

        let mut group = match GroupBuilder::new().init_empty(1, 0) {
            GroupInit::Borrowed(_) => panic!(),
            GroupInit::Init(group) => *group,
        };
        assert!(group.structure_check());

        for i in (0.._K).rev() {
            let mut seq = Sequence::new();
            seq.push(2 * i);
            group.base.push_sequence(2 * i + 2, seq, 0);
        }

        for i in 0..=_BUFFER_SIZE {
            match group.push(i) {
                Ok(_) => {}
                Err(e) => {
                    let mut remaining: Vec<usize> = e.remaining.collect();
                    remaining.sort();
                    assert_eq!(Vec::from_iter(0..=_BUFFER_SIZE), remaining);

                    e.base_group.forced_insert_all(remaining.into_iter());
                }
            }
        }
        group.base.max_seq_len = _BUFFER_SIZE;
        assert!(group.structure_check());
    }
}
