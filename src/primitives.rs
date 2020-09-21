use crate::params::*;

use arrayvec::ArrayVec;
use mem::MaybeUninit;
use std::{
    borrow::Cow, cmp::Ordering, convert::AsRef, fmt::Debug, iter::FromIterator, mem, ops::IndexMut,
    ptr,
};

const _SPLITS: usize = _K - 1;

// ----- lookup table for KDistribute ----- //

lazy_static! {
    static ref TREE_INDEX_LOOKUP: [usize; _SPLITS] = {
        let mut table: MaybeUninit<[usize; _SPLITS]> = MaybeUninit::uninit();
        flat_tree_index_order(_SPLITS)
            .enumerate()
            .for_each(|(i, j)| unsafe { (table.as_mut_ptr() as *mut usize).add(i).write(j) });
        unsafe { table.assume_init() }
    };
}

// ----- splitter primitives ----- //

enum TreeElement {
    Node(usize, usize),
    UnaryNode(usize),
    Leaf,
}

// helper trait for common functionality of R-way and k-way distribute
trait TreeBuffer<T: Ord, R: ?Sized>
where
    R: IndexMut<usize, Output = T>,
{
    fn len(&self) -> usize;

    fn get(&self, index: usize) -> &T {
        if index < self.len() {
            unsafe { self.get_unchecked(index) }
        } else {
            panic!(
                "index out of bounds: the len is {} but the index is {}",
                self.len(),
                index
            )
        }
    }

    fn get_mut(&mut self, index: usize) -> &mut T;

    unsafe fn get_unchecked(&self, index: usize) -> &T;

    /// debugging
    fn structure_check(&self) -> bool {
        let mut el_type = 0;

        (0..self.len())
            .map(|i| match element_type(i, self.len()) {
                TreeElement::Node(left, right) => {
                    self.get(left) <= self.get(i) && self.get(i) <= self.get(right) && el_type == 0
                }
                TreeElement::UnaryNode(left) => {
                    let res = self.get(left) <= self.get(i) && el_type <= 1;
                    el_type = 1;
                    res
                }
                TreeElement::Leaf => {
                    el_type = 2;
                    true
                }
            })
            .all(|x| x)
    }

    fn select_tree_index(&self, splitter_idx: usize) -> usize {
        assert!(self.len() > 0);

        let mut i = 0;
        let (mut min, mut max) = (0, self.len());

        loop {
            let low = ((max - min) / 2 + 1).next_power_of_two() - 1;
            let node_idx = min + low / 2 + usize::min((low + 1) / 2, max - min - low);

            match splitter_idx.cmp(&node_idx) {
                Ordering::Equal => return i,
                Ordering::Less => {
                    max = node_idx;
                    i = 2 * i + 1;
                }
                Ordering::Greater => {
                    min = node_idx + 1;
                    i = 2 * i + 2;
                }
            }
        }
    }

    fn replace_splitter(&mut self, splitter: T, idx: usize) -> T {
        let t_idx = self.select_tree_index(idx);
        mem::replace(self.get_mut(t_idx), splitter)
    }

    /// used for distribute
    unsafe fn next_idx_unchecked(&self, el: &T, idx: usize) -> usize {
        debug_assert!(idx < self.len());
        let is_less = el < self.get_unchecked(idx);
        2 * idx + (if is_less { 1 } else { 2 })
    }
}

// further helper methods
fn element_type(index: usize, len: usize) -> TreeElement {
    let high = len / 2;
    let low = (len - 1) / 2;

    match index {
        i if i < low => TreeElement::Node(2 * i + 1, 2 * i + 2),
        i if i < high => TreeElement::UnaryNode(2 * i + 1),
        i if i < len => TreeElement::Leaf,
        i => panic!("Invalid index: {:?}", i),
    }
}

/// This function assumes that _R < _K always holds, otherwise the search stack will overflow.
fn flat_tree_index_order(len: usize) -> TreeIndexIter {
    TreeIndexIter {
        len,
        stack: if len > 0 {
            let mut vec = Vec::new();
            vec.push((0, DFSLabel::from(element_type(0, len))));
            vec
        } else {
            Vec::new()
        },
    }
}

enum DFSLabel {
    Both(usize, usize),
    Left(usize),
    Right(usize),
    None,
}

impl From<TreeElement> for DFSLabel {
    fn from(el: TreeElement) -> Self {
        match el {
            TreeElement::Node(l, r) => DFSLabel::Both(l, r),
            TreeElement::UnaryNode(l) => DFSLabel::Left(l),
            TreeElement::Leaf => DFSLabel::None,
        }
    }
}

struct TreeIndexIter {
    len: usize,
    // suffices for KDistribute and for RDistribute, as R <= K for any reasonable input size
    stack: Vec<(usize, DFSLabel)>,
}

impl Iterator for TreeIndexIter {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (i, state) = self.stack.pop()?;

            match state {
                DFSLabel::Both(left, right) => {
                    self.stack.push((i, DFSLabel::Right(right)));
                    self.stack
                        .push((left, DFSLabel::from(element_type(left, self.len))));
                }
                DFSLabel::Left(left) => {
                    self.stack.push((i, DFSLabel::None));
                    self.stack
                        .push((left, DFSLabel::from(element_type(left, self.len))));
                }
                DFSLabel::Right(right) => {
                    self.stack
                        .push((right, DFSLabel::from(element_type(right, self.len))));
                    return Some(i);
                }
                DFSLabel::None => return Some(i),
            }
        }
    }
}

impl<T: Ord> TreeBuffer<T, [T]> for [T; _SPLITS] {
    fn len(&self) -> usize {
        _SPLITS
    }

    fn get_mut(&mut self, index: usize) -> &mut T {
        &mut self[index]
    }

    unsafe fn get_unchecked(&self, index: usize) -> &T {
        self.as_ref().get_unchecked(index)
    }
}

// TODO: many identical elements currently lead to bad performance
pub(crate) struct KDistribute<T: Ord> {
    tree: [T; _SPLITS],
}

impl<T: Ord> KDistribute<T> {
    // Unfortunately, the compiler can not eliminate the branch in the more general version
    // of the r-distribute. Thus a little code duplication is unavoidable.
    pub fn distribute(&self, el: &T) -> usize {
        let len = self.tree.len();

        let mut idx = 0;
        for _ in 0..(len.count_ones()) {
            // compiler seems unable to completely remove bound checks
            idx = unsafe { self.tree.next_idx_unchecked(el, idx) };
        }

        let result = idx - len;
        debug_assert!(result <= len, "Invalid result: {:?}", result);
        result
    }

    pub fn splitter_at(&self, idx: usize) -> &T {
        debug_assert!(idx < self.tree.len());
        let t_idx = TREE_INDEX_LOOKUP[idx];
        self.tree.get(t_idx)
    }

    pub fn replace_splitter(&mut self, splitter: T, idx: usize) -> T {
        debug_assert!(idx < self.tree.len());
        let t_idx = TREE_INDEX_LOOKUP[idx];
        mem::replace(self.tree.get_mut(t_idx), splitter)
    }

    /// Replaces the splitter at the specified index, shifting either the smaller
    /// or bigger half of the remaining splitters and returning the removed splitter.
    pub fn insert_splitter_at(&mut self, splitter: T, idx: usize, leftwards: bool) -> T {
        let mut exchanged = splitter;
        let indizes: ArrayVec<[usize; _SPLITS]> = if leftwards {
            (0..=idx).rev().collect()
        } else {
            (idx.._SPLITS).collect()
        };
        for i in indizes {
            let t_idx = TREE_INDEX_LOOKUP[i];
            exchanged = mem::replace(&mut self.tree[t_idx], exchanged);
        }
        debug_assert!(self.tree.structure_check());
        exchanged
    }

    /// debugging
    pub fn structure_check(&self) -> bool {
        self.tree.structure_check()
    }
}

impl<'a, T: 'a + Ord + Clone> KDistribute<T> {
    pub fn new(splitters: &[T]) -> Self {
        debug_assert!({
            let mut vec = splitters.to_owned();
            vec.sort();
            vec.as_slice() == splitters
        });
        debug_assert!(!splitters.is_empty() && splitters.len() < _K);

        let mut splitters = Cow::Borrowed(splitters);
        if splitters.len() < _SPLITS {
            let owned = splitters.to_mut();
            owned.reserve_exact(_SPLITS - owned.len());
            // can not fail as splitters is not empty
            let filler = owned.first().unwrap().clone();
            for _ in 0.._SPLITS - owned.len() {
                owned.insert(0, filler.clone());
            }
        }
        debug_assert!(splitters.len() == _SPLITS);

        let mut tree: MaybeUninit<[T; _SPLITS]> = MaybeUninit::uninit();
        for i in 0.._SPLITS {
            unsafe {
                (tree.as_mut_ptr() as *mut T)
                    .add(TREE_INDEX_LOOKUP[i])
                    .write(splitters[i].clone());
            }
        }
        let tree = unsafe { tree.assume_init() };

        debug_assert!(tree.structure_check());
        Self { tree }
    }

    pub fn into_iter(self) -> impl Iterator<Item = T> + 'a {
        flat_tree_index_order(_SPLITS).map(move |i| self.tree[i].clone())
    }
}

impl<T: Debug + Ord> Debug for KDistribute<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        (&self.tree as &[T]).fmt(f)
    }
}

impl<T: Ord> TreeBuffer<T, [T]> for Vec<T> {
    fn len(&self) -> usize {
        self.len()
    }

    fn get_mut(&mut self, index: usize) -> &mut T {
        &mut self[index]
    }

    unsafe fn get_unchecked(&self, index: usize) -> &T {
        self.as_slice().get_unchecked(index)
    }
}

#[derive(Debug)]
pub(crate) struct RDistribute<T: Ord> {
    tree: Vec<T>,
}

impl<T: Ord> RDistribute<T> {
    pub fn new() -> Self {
        Self { tree: Vec::new() }
    }

    pub fn distribute(&self, el: &T) -> usize {
        let len = self.tree.len();
        let high = (len + 1).next_power_of_two() - 1;

        if len == 0 {
            return 0;
        }

        let mut idx = 0;
        for _ in 0..(high.count_ones() - 1) {
            // compiler seems unable to completely remove bound checks
            idx = unsafe { self.tree.next_idx_unchecked(el, idx) };
        }

        let result = {
            if idx < len {
                idx = unsafe { self.tree.next_idx_unchecked(el, idx) };
                idx - high
            } else {
                idx + len + 1 - high
            }
        };

        debug_assert!(result <= len, "Invalid result: {:?}", result);
        result
    }

    pub fn splitter_at(&self, idx: usize) -> &T {
        debug_assert!(idx < self.tree.len());
        let tree_idx = self.tree.select_tree_index(idx);
        self.tree.get(tree_idx)
    }

    pub fn replace_splitter(&mut self, splitter: T, idx: usize) -> T {
        debug_assert!(idx < self.tree.len());
        self.tree.replace_splitter(splitter, idx)
    }

    /// debugging
    pub fn structure_check(&self) -> bool {
        self.tree.structure_check()
    }
}

impl<T: Ord + Clone> RDistribute<T> {
    /// adds a splitter at the last index by rebuilding the complete tree
    pub fn add_splitter(&mut self, s: T) {
        let mut buffer = Vec::<T>::new();
        buffer.resize(self.tree.len(), s.clone());

        flat_tree_index_order(self.tree.len())
            .enumerate()
            .for_each(|(i, j)| buffer[i] = self.tree[j].clone());
        self.tree.push(s.clone());
        buffer.push(s);
        flat_tree_index_order(self.tree.len())
            .enumerate()
            .for_each(|(i, j)| self.tree[j] = buffer[i].clone());

        debug_assert!(self.tree.structure_check());
    }
    /// removes the last splitter by rebuilding the complete tree
    pub fn remove_splitter(&mut self) {
        let mut buffer = Vec::<T>::new();
        buffer.resize(self.tree.len(), self.tree[0].clone());

        flat_tree_index_order(self.tree.len())
            .enumerate()
            .for_each(|(i, j)| buffer[i] = self.tree[j].clone());
        self.tree.pop();
        buffer.pop();
        flat_tree_index_order(self.tree.len())
            .enumerate()
            .for_each(|(i, j)| self.tree[j] = buffer[i].clone());

        debug_assert!(self.tree.structure_check());
    }

    pub fn len(&self) -> usize {
        self.tree.len()
    }
}

// ----- sequence and group buffer primitives ----- //

#[derive(Debug)]
// TODO: more efficient implementation regarding allocations
pub(crate) struct Sequence<T: Ord> {
    data: Vec<T>,
}

impl<T: Ord> Sequence<T> {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            data: Vec::with_capacity(capacity),
        }
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn push(&mut self, el: T) {
        self.data.push(el)
    }

    pub fn append(&mut self, other: &mut Self) {
        self.data.append(&mut other.data)
    }

    // TODO: inefficient for some cases? (unnecessary I/O)
    pub fn drain(&mut self) -> impl Iterator<Item = T> + '_ {
        self.data.drain(0..)
    }

    pub fn as_vec(&mut self) -> &mut Vec<T> {
        &mut self.data
    }

    // #[cfg(any(debug, test))]
    pub fn min(&self) -> Option<&T> {
        self.data.iter().min()
    }

    // #[cfg(any(debug, test))]
    pub fn max(&self) -> Option<&T> {
        self.data.iter().max()
    }
}

impl<T: Ord> Default for Sequence<T> {
    fn default() -> Self {
        Self { data: Vec::new() }
    }
}

impl<T: Ord> FromIterator<T> for Sequence<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self {
            data: Vec::from_iter(iter),
        }
    }
}

#[derive(Debug)]
pub(crate) struct GroupBuffer<T> {
    data: ArrayVec<[T; _BUFFER_SIZE]>,
}

impl<T: Ord> GroupBuffer<T> {
    pub fn new() -> Self {
        Self {
            data: ArrayVec::new(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    pub fn is_full(&self) -> bool {
        self.data.is_full()
    }

    // TODO: is a second bounds check elided?
    pub fn push(&mut self, el: T) {
        self.data.push(el)
    }

    pub fn drain(&mut self) -> impl Iterator<Item = T> + '_ {
        self.data.drain(0..)
    }

    // #[cfg(any(debug, test))]
    pub fn min(&self) -> Option<&T> {
        self.data.iter().min()
    }

    // #[cfg(any(debug, test))]
    pub fn max(&self) -> Option<&T> {
        self.data.iter().max()
    }

    pub fn count(&self) -> usize {
        self.data.len()
    }
}

#[derive(Debug)]
pub(crate) struct BHeap<T: Ord> {
    data: [T; _M],
    len: usize,
}

impl<T: Ord> BHeap<T> {
    pub fn new() -> Self {
        Self {
            data: unsafe { mem::zeroed() },
            len: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn peek(&self) -> &T {
        debug_assert!(self.len > 0);
        &self.data[0]
    }

    pub fn pop(&mut self) -> T {
        debug_assert!(self.len > 0);
        // TODO: can the compiler elide this check? -> seems not
        assert!(self.len <= _M);

        let mut val = unsafe { (&self.data[self.len - 1] as *const T).read() };
        mem::swap(&mut self.data[0], &mut val);
        self.sift_down(0);
        self.len -= 1;
        val
    }

    pub fn push(&mut self, el: T) {
        debug_assert!(self.len < _M);
        let mut pos = self.len;
        unsafe { (&mut self.data[pos] as *mut T).write(el) };
        self.len += 1;

        while pos > 0 {
            unsafe {
                let next_pos = (pos - 1) / 2;
                if self.data.get_unchecked(pos) < self.data.get_unchecked(next_pos) {
                    ptr::swap_nonoverlapping(
                        self.data.get_unchecked_mut(pos),
                        self.data.get_unchecked_mut(next_pos),
                        1,
                    );
                    pos = next_pos;
                } else {
                    return;
                }
            }
        }
    }

    pub fn refill_from_sequence(&mut self, seq: &mut Sequence<T>) {
        debug_assert!(self.len == 0);
        debug_assert!(seq.len() <= _M);
        for el in seq.drain() {
            unsafe { (&mut self.data[self.len] as *mut T).write(el) };
            self.len += 1;
        }
        if self.len >= 4 {
            self.recursive_build(0, self.len / 8, self.len / 4 - 1);
        } else {
            self.build_base(0, true, true);
        }
    }

    pub fn get_as_vec(&mut self) -> Vec<T> {
        assert!(self.len <= _M);
        let mut vec = Vec::with_capacity(self.len);
        for i in 0..self.len {
            vec.push(unsafe { (&self.data[i] as *const T).read() });
        }
        self.len = 0;
        vec
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> {
        assert!(self.len <= _M);
        self.data[0..self.len].iter()
    }

    fn sift_down(&mut self, mut pos: usize) {
        let range = ((self.len + 1).next_power_of_two() / 2) - 1;

        let mut left_child = 2 * pos + 1;
        while left_child < range {
            unsafe {
                let right_child = left_child + 1;
                let next_pos = left_child
                    + if self.data.get_unchecked(left_child) < self.data.get_unchecked(right_child)
                    {
                        0
                    } else {
                        1
                    };
                let current_val: *mut _ = self.data.get_unchecked_mut(pos);
                let next_val: *mut _ = self.data.get_unchecked_mut(next_pos);
                if *current_val <= *next_val {
                    return;
                }

                ptr::swap_nonoverlapping(current_val, next_val, 1);
                pos = next_pos;
                left_child = 2 * pos + 1;
            }
        }

        if left_child < self.len {
            unsafe {
                let mut child = left_child + 1;
                if child >= self.len
                    || self.data.get_unchecked(left_child) < self.data.get_unchecked(child)
                {
                    child = left_child;
                }
                let current_val: *mut _ = self.data.get_unchecked_mut(pos);
                let next_val: *mut _ = self.data.get_unchecked_mut(child);
                if *next_val < *current_val {
                    ptr::swap_nonoverlapping(current_val, next_val, 1);
                }
            }
        }
    }

    fn recursive_build(&mut self, idx: usize, range_lower: usize, range_upper: usize) {
        let left_child = 2 * idx + 1;
        let right_child = 2 * idx + 2;
        debug_assert!(idx < self.len);
        debug_assert!(left_child < self.len);

        // base case
        if idx >= range_lower {
            debug_assert!(idx <= range_upper);
            if idx == range_upper {
                self.build_base(left_child, true, true);
                self.build_base(right_child, true, true);
            } else {
                self.build_base(left_child, false, false);
                self.build_base(right_child, false, false);
            }
        } else {
            self.recursive_build(left_child, range_lower, range_upper);
            if right_child <= range_upper {
                self.recursive_build(right_child, range_lower, range_upper);
            } else if idx + 1 == range_lower {
                self.build_base(right_child, false, false);
            }
        }
        self.sift_down(idx);
    }

    #[inline(always)]
    fn build_base(&mut self, idx: usize, check_left: bool, check_right: bool) {
        let left_child = 2 * idx + 1;
        if !check_left || (left_child < self.len) {
            unsafe {
                let mut child = left_child + 1;
                if (check_right && child >= self.len)
                    || self.data.get_unchecked(left_child) < self.data.get_unchecked(child)
                {
                    child = left_child;
                }
                let current_val: *mut _ = self.data.get_unchecked_mut(idx);
                let next_val: *mut _ = self.data.get_unchecked_mut(child);
                if *next_val < *current_val {
                    ptr::swap_nonoverlapping(current_val, next_val, 1);
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::iter::FromIterator;

    #[test]
    fn basic_kway() {
        let splitters = &Vec::from_iter(1.._K);
        let distr = KDistribute::<usize>::new(splitters);

        for i in 1.._K {
            assert_eq!(i, distr.distribute(&i));
            assert_eq!(i, *distr.splitter_at(i - 1));
        }
    }

    #[test]
    fn basic_rway() {
        let mut distr = RDistribute::<usize>::new();
        assert_eq!(0, distr.distribute(&1));

        for i in 1..usize::min(_K, 10) {
            distr.add_splitter(i);

            for j in 1..i {
                assert_eq!(j, distr.distribute(&j));
                assert_eq!(j, *distr.splitter_at(j - 1));
            }
        }
    }

    #[test]
    fn move_subtree() {
        if _K < 8 {
            return;
        }

        let splitters = &Vec::from_iter(1.._K);
        let mut distr = KDistribute::<usize>::new(splitters);

        assert_eq!(_SPLITS, distr.insert_splitter_at(0, 0, false));
        assert_eq!(_SPLITS - 1, distr.insert_splitter_at(1, 1, false));
        assert_eq!(_SPLITS - 2, distr.insert_splitter_at(2, 3, false));
        assert_eq!(
            _SPLITS - 3,
            distr.replace_splitter(2 * _SPLITS + 3, _SPLITS - 1)
        );
        assert!(distr.structure_check());
        assert_eq!(2 * _SPLITS + 3, distr.insert_splitter_at(0, 0, false));
    }

    #[test]
    fn traverse_kway() {
        use std::iter::FromIterator;

        let splitters = &Vec::from_iter(0.._K - 1);
        let distr = KDistribute::<usize>::new(splitters);

        check_traverse(&distr.tree);
        assert_eq!(*splitters, distr.into_iter().collect::<Vec<usize>>());
    }

    #[test]
    fn traverse_rway() {
        let mut distr = RDistribute::<usize>::new();

        for i in 1..usize::min(_K, 10) {
            distr.add_splitter(i);
            check_traverse(&distr.tree);
        }
    }

    fn check_traverse<R: ?Sized + IndexMut<usize, Output = usize>>(
        tree: &impl TreeBuffer<usize, R>,
    ) {
        flat_tree_index_order(tree.len())
            .enumerate()
            .for_each(|(i, j)| assert_eq!(j, tree.select_tree_index(i)));
    }

    #[test]
    fn test_sequence() {
        let mut seq = Sequence::<usize>::new();
        assert_eq!(seq.len(), 0);
        seq.push(1);
        seq.push(3);
        assert_eq!(*seq.min().unwrap(), 1);
        seq.push(0);
        assert_eq!(*seq.min().unwrap(), 0);
        assert_eq!(*seq.max().unwrap(), 3);
        assert_eq!(seq.len(), 3);

        let mut other = Sequence::<usize>::new();
        other.push(7);
        other.push(6);
        seq.append(&mut other);
        assert_eq!(other.len(), 0);
        assert_eq!(seq.len(), 5);

        seq.drain()
            .zip(vec![1, 3, 0, 7, 6].into_iter())
            .for_each(|(x, y)| assert_eq!(x, y));
    }

    #[test]
    fn test_buffer() {
        let mut buf = GroupBuffer::<usize>::new();
        assert!(buf.is_empty());
        assert!(!buf.is_full());
        buf.push(1);
        assert!(!buf.is_empty());
        buf.push(3);
        assert_eq!(*buf.min().unwrap(), 1);
        buf.push(0);
        assert_eq!(*buf.min().unwrap(), 0);
        assert_eq!(*buf.max().unwrap(), 3);

        buf.drain()
            .zip(vec![1, 3, 0].into_iter())
            .for_each(|(x, y)| assert_eq!(x, y));
    }

    #[test]
    fn lookup_table() {
        let splitters = &vec![0; _SPLITS];
        let distr = KDistribute::<usize>::new(splitters);
        for i in 0.._SPLITS {
            assert_eq!(TREE_INDEX_LOOKUP[i], distr.tree.select_tree_index(i));
        }
    }

    #[test]
    fn insert_splitter_at_test() {
        let splitters = &Vec::from_iter(0.._K - 1);
        let mut distr = KDistribute::<usize>::new(splitters);

        distr.insert_splitter_at(_K / 2, _K / 2, true);
        distr.insert_splitter_at(_K / 2, _K / 2, false);
        assert_eq!(*distr.splitter_at(0), 1);
        assert_eq!(*distr.splitter_at(_SPLITS - 1), _SPLITS - 2);
    }

    #[test]
    fn test_bheap_basic() {
        let mut bheap = BHeap::new();
        bheap.push(0);
        bheap.push(1);
        bheap.push(3);
        bheap.push(2);
        bheap.push(4);

        assert_eq!(bheap.pop(), 0);
        assert_eq!(bheap.pop(), 1);
        assert_eq!(bheap.pop(), 2);
        assert_eq!(bheap.pop(), 3);
        assert_eq!(bheap.pop(), 4);

        for i in (0.._M).rev() {
            bheap.push(i);
        }
        for i in 0.._M {
            assert_eq!(bheap.pop(), i);
        }
    }

    #[test]
    fn test_bheap_refill() {
        let mut bheap = BHeap::new();
        for i in 0..=_M {
            let mut seq = Sequence::new();
            for j in (0..i).rev() {
                seq.push(j);
            }
            bheap.refill_from_sequence(&mut seq);
            for j in 0..i {
                assert_eq!(bheap.pop(), j);
            }
        }
    }
}
