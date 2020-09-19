use crate::{dbg_assertion, groups::*, params::*, primitives::*};
use arrayvec::ArrayVec;
use rand::{Rng, SeedableRng};
use rand_pcg::Pcg32;
use smallvec::SmallVec;
use std::{fmt::Debug, iter, iter::FromIterator, mem};

type Rand = Pcg32;

// TODO replace Iterator with IntoIter in arguments

// ----- Implementation using an insertion heap as buffer -----
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

// ----- Implementation without buffer -----
#[derive(Debug)]
pub struct FlatHeap<T: Ord + Clone> {
    len: usize,
    groups: Groups<T>,
}

impl<T: Ord + Clone> FlatHeap<T> {
    pub fn new() -> Self {
        Self {
            len: 0,
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
            self.groups.deletion_heap.is_empty()
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

        let result = self.groups.deletion_heap.pop();
        if result.is_some() {
            self.len -= 1;
        }
        result
    }

    pub fn push(&mut self, el: T) {
        self.groups.insert_all(iter::once(el));
        self.len += 1;
    }
}

/// helper struct for gracefully traversing the groups without lifetime issues
#[derive(Debug)]
struct GroupCursor<'a, T: Ord + Clone> {
    idx: usize,
    group: &'a mut BufferedGroup<T>,
    tail: &'a mut [Box<BufferedGroup<T>>],
}

impl<'a, T: Ord + Clone> GroupCursor<'a, T> {
    fn new(groups: &'a mut [Box<BufferedGroup<T>>]) -> Option<Self> {
        groups.split_first_mut().map(|(group, tail)| Self {
            idx: 0,
            group,
            tail,
        })
    }

    fn step(idx: usize, tail: &'a mut [Box<BufferedGroup<T>>]) -> Option<Self> {
        tail.split_first_mut().map(|(group, tail)| Self {
            idx: idx + 1,
            group,
            tail,
        })
    }

    fn split<'b>(&'b mut self) -> GroupCursor<'b, T> {
        GroupCursor::<'b, T> {
            idx: self.idx,
            group: self.group,
            tail: self.tail,
        }
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

        while let Some(cursor) = GroupCursor::new(&mut self.group_list) {
            match Self::pull_non_empty_sequence(&mut self.rng, &mut self.r_distr, cursor, _M) {
                Ok(Some(seq)) => {
                    for el in seq.drain() {
                        // can not fail as one sequence of the first group always fits into the heap
                        self.deletion_heap.push(el).ok().unwrap()
                    }
                    break;
                }
                Ok(None) => break,
                Err((group_idx, seq_idx)) => self.handle_group_overflow(group_idx, seq_idx),
            }
        }
        dbg_assertion!(self.structure_check());
    }

    fn refill_group(
        rng: &mut Rand,
        r_distr: &mut RDistribute<T>,
        cursor: GroupCursor<T>,
    ) -> Result<(), (usize, usize)> {
        if let Some(mut next) = GroupCursor::step(cursor.idx, cursor.tail) {
            let max_elements = next.group.max_seq_len();

            if let Some(seq) =
                Self::pull_non_empty_sequence(rng, r_distr, next.split(), max_elements)?
            {
                let mut refill_sequence = mem::replace(seq, Sequence::new());
                let mut max_elements =
                    max_elements - usize::min(refill_sequence.len(), max_elements);

                // TODO: avoid unnecessary copies
                while let Some(seq) =
                    Self::pull_non_empty_sequence(rng, r_distr, next.split(), max_elements)?
                {
                    max_elements -= seq.len();
                    refill_sequence.append(seq);
                }

                // buffer is empty as a precondition of this function
                let base_group = cursor.group.base_group();
                Self::refill_group_from_sequence(rng, base_group, &mut refill_sequence);

                Self::scan_and_split(rng, base_group).map(|(mut splitters, sequences)| {
                    // can not fail because scan_and_split does not return an empty iterator
                    let splitter = splitters.next_back().unwrap();

                    // edge case: last group was removed by pull_non_empty_sequence
                    if next.idx == r_distr.len() {
                        r_distr.add_splitter(splitter.clone());
                    }
                    Self::insert_sequences_to_group(
                        r_distr, next.idx, next.group, splitter, splitters, sequences,
                    );
                });
            }

            dbg_assertion!(cursor.group.structure_check());
        }
        Ok(())
    }

    /// Tries to retrieve a sequence from the group with the given index,
    /// recursively calling refill_group if necessary. Additionally adjusts the splitters.
    fn pull_non_empty_sequence<'a>(
        rng: &mut Rand,
        r_distr: &mut RDistribute<T>,
        mut cursor: GroupCursor<'a, T>,
        max_elements: usize,
    ) -> Result<Option<&'a mut Sequence<T>>, (usize, usize)> {
        if let Some(i) = Self::resolve_overflow(cursor.group.clear_buffer()) {
            return Err((cursor.idx, i));
        }
        let base_group = cursor.group.base_group();
        if base_group.is_empty() {
            Self::refill_group(rng, r_distr, cursor.split())?;
        }

        let base_group = cursor.group.base_group();
        base_group.pop_empty();
        if let (splitter, Some(seq)) = base_group.pop_sequence_if(|s| s.len() <= max_elements) {
            if seq.len() > 0 {
                let idx = cursor.idx;
                match splitter {
                    Some(s) => Some(s),
                    None => {
                        if r_distr.len() == cursor.idx + 1 {
                            // TODO: cache groups to avoid unnecessary allocation?
                            // self.group_list.pop();
                            r_distr.remove_splitter();
                            None
                        } else {
                            Some(r_distr.splitter_at(cursor.idx + 1).clone())
                        }
                    }
                }
                .map(|splitter| {
                    r_distr.replace_splitter(splitter, idx);
                });
                return Ok(Some(seq));
            }
        }
        Ok(None)
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
        r_distr: &mut RDistribute<T>,
        group_idx: usize,
        group: &mut BufferedGroup<T>,
        splitter: T,
        splitters: impl Iterator<Item = T>,
        sequences: impl Iterator<Item = Sequence<T>>,
    ) {
        // TODO: incorrect order?!
        debug_assert!(group_idx < r_distr.len());
        debug_assert!(splitter <= *r_distr.splitter_at(group_idx));

        let first_splitter = r_distr.replace_splitter(splitter.clone(), group_idx);
        let iter = iter::once(first_splitter).chain(splitters).zip(sequences);

        // push new sequences to the group
        let max_seq_len = group.max_seq_len();
        for (split, mut seq) in iter {
            let num_seqs = group.num_sequences();

            // TODO: What is the right strategy for filling a group?
            // Maybe sequences should be filled only to half?
            let first_seq = group.first_or_insert();
            if num_seqs == _K || first_seq.len() + seq.len() <= max_seq_len {
                first_seq.append(&mut seq);
            } else {
                group.push_sequence(split, seq, splitter.clone());
            }
        }

        dbg_assertion!(group.first_or_insert().len() > max_seq_len || group.structure_check());
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

        if self.r_distr.len() == 0 {
            // if the first group does not exist yet, initialize it from the deletion heap
            let step = (_M + 1) as f64 / (_K + 1) as f64;
            let first = step.round() as usize;
            let splitters: Vec<T> = (2..=_K)
                .map(|i| elements[(i as f64 * step).round() as usize].clone())
                .collect();

            self.push_group(elements[first].clone(), |b| {
                b.init_from_splitters(max_seq_len, &splitters)
            })
            .forced_insert_all(elements.drain(first..elements.len()));
        } else {
            // otherwise, push half of the elements into the first group
            let mid = elements.len() / 2;
            let splitter = elements[mid].clone();
            let seq = Sequence::from_iter(elements.drain((mid + 1)..elements.len()));
            let group = &mut self.group_list[0];
            Self::insert_sequences_to_group(
                &mut self.r_distr,
                0,
                group,
                splitter,
                None.into_iter(),
                iter::once(seq),
            );

            // handle overflow
            if group.first_or_insert().len() > max_seq_len {
                self.handle_group_overflow(0, 0);
            }
        }

        for el in elements.into_iter() {
            // can not fail as the heap was emptied
            self.deletion_heap.push(el).ok().unwrap();
        }

        dbg_assertion!(self.structure_check());
    }

    fn handle_group_overflow(&mut self, group_idx: usize, seq_idx: usize) {
        debug_assert!(group_idx < self.r_distr.len() && seq_idx < _K);
        let num_groups = self.r_distr.len();
        let base_group = self.group_list[group_idx].clear_buffer_forced();
        let max_seq_len = base_group.max_seq_len();

        // split the overflowing sequence, removing the biggest sequence from the group
        let (big_splitter, big_sequence) = Self::split_in_two(&mut self.rng, base_group, seq_idx)
            .map_or((None, None), |(s, seq)| (Some(s), Some(seq)));
        let n_skip = _K - base_group.num_sequences() + 1;

        // can not fail as at least two sequences are present
        let res = base_group.pop_sequence();
        let small_splitter = res.0.unwrap();
        let mut elements = mem::replace(res.1.unwrap(), Sequence::new());
        let mut new_group =
            match GroupBuilder::new().init_empty(max_seq_len, small_splitter.clone()) {
                GroupInit::Borrowed(_) => unimplemented!(),
                GroupInit::Init(group) => group,
            };
        let overflow = {
            let base_group = new_group.as_mut().base_group();
            Self::refill_group_from_sequence(&mut self.rng, base_group, &mut elements);
            base_group.scan_for_overflow(0)
        };
        let (splitters, sequences) =
            mem::replace(&mut self.group_list[group_idx], new_group).into_sequences();

        // now, move the remaining sequences to the next group
        let sequences = sequences.chain(big_sequence);
        let splitters = splitters.skip(n_skip).chain(big_splitter);
        if group_idx + 1 == num_groups {
            // if the next group does not exist yet, initialize it with the available sequences
            let splitters: Vec<T> = splitters.collect();
            self.push_group(small_splitter.clone(), |b| {
                b.init_from_iter(
                    _SCALING * max_seq_len,
                    &splitters,
                    sequences,
                    small_splitter,
                )
            });
        } else {
            let group = &mut self.group_list[group_idx + 1];
            Self::insert_sequences_to_group(
                &mut self.r_distr,
                group_idx + 1,
                group,
                small_splitter,
                splitters.collect::<Vec<_>>().into_iter().rev(),
                sequences.rev(),
            );

            // handle overflow
            if group.first_or_insert().len() > group.max_seq_len() {
                self.handle_group_overflow(group_idx, 0);
            }
        }

        // it is very, really, extremely unlikely that an overflow happens here
        overflow.map(|seq_idx| self.handle_group_overflow(group_idx, seq_idx));

        dbg_assertion!(self.group_list[group_idx].structure_check());
    }

    // TODO: set initial capacity of vecs to avoid unnecessary allocation?
    fn push_group<F>(&mut self, splitter: T, f: F) -> &mut BaseGroup<T>
    where
        F: FnOnce(GroupBuilder<T>) -> GroupInit<T>,
    {
        self.r_distr.add_splitter(splitter);
        if self.group_list.len() < self.r_distr.len() {
            match f(GroupBuilder::new()) {
                GroupInit::Borrowed(_) => unreachable!(),
                GroupInit::Init(group) => {
                    self.group_list.push(group);
                    self.group_list.last_mut().unwrap().as_mut().base_group()
                }
            }
        } else {
            match f(GroupBuilder::borrowed(self.group_list[0].as_mut())) {
                GroupInit::Borrowed(group) => group.base_group(),
                GroupInit::Init(_) => unreachable!(),
            }
        }
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
        let mut elements = mem::replace(small_seq, Sequence::new());
        let splitter = {
            let mut sample = Self::choose_sample(rng, &elements.as_vec());
            sample.sort();
            sample[_SAMPLING_SIZE / 2].clone()
        };

        for el in elements.drain() {
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
        seq: &mut Sequence<T>,
    ) {
        debug_assert!(base_group.is_empty());
        if seq.len() == 0 {
            return;
        }

        let elements = seq.as_vec();
        let new_splitters: ArrayVec<[T; _K - 1]> = {
            // TODO: in theory, this could be replaced with an ArrayVec
            let mut sample: Vec<T> = Vec::new();
            for _ in 0..((_K - 1) * _SAMPLING_COUNT) {
                sample.extend(Self::choose_sample(rng, &elements));
            }
            debug_assert!(sample.len() == (_K - 1) * _SAMPLING_SIZE * _SAMPLING_COUNT);
            let skip = _SAMPLING_SIZE * _SAMPLING_COUNT;
            sample.sort();
            sample
                .into_iter()
                .skip(skip / 2)
                .step_by(skip)
                .collect()
        };
        debug_assert!((new_splitters.len() == _K - 1));

        base_group.replace_splitters(&new_splitters);
        base_group.forced_insert_all(elements.drain(0..elements.len()));
    }

    /// Returns removed sequences and splitters in decreasing order.
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

    fn choose_sample<'a>(rng: &mut Rand, elements: &'a [T]) -> ArrayVec<[T; _SAMPLING_SIZE]> {
        debug_assert!(!elements.is_empty());
        let num_steps = elements.len() / _SAMPLING_SIZE;
        let result: ArrayVec<[T; _SAMPLING_SIZE]> = if num_steps == 0 {
            iter::repeat(elements)
                .flat_map(|els| els.iter().cloned())
                .take(_SAMPLING_SIZE)
                .collect()
        } else {
            let step_idx = rng.gen_range(0, num_steps);
            let start = _SAMPLING_SIZE * step_idx;
            elements[start..(start + _SAMPLING_SIZE)]
                .iter()
                .cloned()
                .collect()
        };

        assert!(result.len() == _SAMPLING_SIZE);
        result
    }

    // #[cfg(any(debug, test))]
    pub fn structure_check(&self) -> bool {
        assert!(self.group_list.len() >= self.r_distr.len());

        let mut valid = self.r_distr.structure_check();
        let mut prev_max = self.deletion_heap.max();
        for i in 0..self.r_distr.len() {
            let group = &self.group_list[i];
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
    fn heaps_only() {
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
    fn deletion_heap_overflow() {
        let mut s_heap = SampleHeap::new();

        for i in (0.._M).chain((0.._M).rev()).chain(0..=_M) {
            s_heap.push(i);
        }
        assert!(s_heap.groups.structure_check());
    }

    #[test]
    fn group_overflow() {
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
    fn group_overflow_reverse() {
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
    fn refill_edge_case() {
        let mut s_heap = SampleHeap::new();

        for _ in (0..(4 * _M)).rev() {
            s_heap.push(0);
        }
        assert!(s_heap.groups.structure_check());

        while let Some(_) = s_heap.pop() {}
        assert!(s_heap.is_empty());
    }

    // #[test]
    // fn insert_sequences() {
    //     let mut s_heap = SampleHeap::new();

    //     for _ in 0..=(2 * _M) {
    //         s_heap.push(2);
    //     }

    //     let mut s0 = Sequence::new();
    //     for _ in 0.._M {
    //         s0.push(0);
    //     }
    //     let mut s1 = Sequence::new();
    //     for _ in 0.._M {
    //         s1.push(1);
    //     }
    //     let mut seqs = vec![s1, s0];

    //     loop {
    //         s_heap.pop();
    //         if s_heap.groups.deletion_heap.is_empty() {
    //             let group = s_heap.groups.group_list[0];
    //             let mut overflow =
    //             Groups::resolve_overflow(group.clear_buffer()).map(|i| (0, i));
    //             let base_group = group.base_group();
    //             while base_group.num_sequences() > 1 {
    //                 base_group.pop_sequence();
    //             }
    //             s_heap.groups.insert_sequences_to_group(
    //                 0,
    //                 0,
    //                 iter::once(1),
    //                 seqs.drain(0..seqs.len()),
    //             );
    //             break;
    //         }
    //     }
    //     assert!(s_heap.groups.structure_check());
    // }
}
