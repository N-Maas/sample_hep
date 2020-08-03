use crate::params::*;

use arrayvec::ArrayVec;
use mem::MaybeUninit;
use smallvec::SmallVec;
use std::{cmp::Ordering, convert::AsRef, fmt::Debug, iter::FromIterator, mem, ops::IndexMut};

const _SPLITS: usize = _K - 1;

// ----- splitter primitives ----- //

pub(crate) trait Distribute<T: Ord> {
    fn distribute(&self, el: &T) -> usize;

    fn splitter_at(&self, idx: usize) -> &T;

    fn insert_splitter(&mut self, splitter: T) -> T;

    fn replace_splitter(&mut self, splitter: T, idx: usize) -> T;

    fn structure_check(&self) -> bool;
}

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

    /// Inserts the splitter at the appropriate position, moving the remaining splitters to the right and returning the largest one.
    fn insert_splitter_at_idx(&mut self, splitter: T, idx: usize) -> T {
        debug_assert!(idx < self.len());
        let el_type = element_type(idx, self.len());

        if splitter < *self.get(idx) {
            match el_type {
                TreeElement::Leaf => mem::replace(self.get_mut(idx), splitter),
                TreeElement::UnaryNode(left) | TreeElement::Node(left, _) => {
                    let new = self.insert_splitter_at_idx(splitter, left);
                    let old = mem::replace(self.get_mut(idx), new);

                    if let TreeElement::Node(_, right) = el_type {
                        // causes unnecessary comparisons
                        self.insert_splitter_at_idx(old, right)
                    } else {
                        old
                    }
                }
            }
        } else {
            match el_type {
                TreeElement::UnaryNode(_) | TreeElement::Leaf => splitter,
                TreeElement::Node(_, right) => self.insert_splitter_at_idx(splitter, right),
            }
        }
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
            let mut vec = ArrayVec::new();
            vec.push((0, DFSLabel::from(element_type(0, len))));
            vec
        } else {
            ArrayVec::new()
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
    stack: ArrayVec<[(usize, DFSLabel); _SPLITS.count_ones() as usize]>,
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

pub(crate) struct KDistribute<T: Ord> {
    tree: [T; _SPLITS],
}

impl<T: Ord + Clone> KDistribute<T> {
    pub fn new(splitters: &[T]) -> Self {
        debug_assert!({
            let mut vec = splitters.to_owned();
            vec.sort();
            vec.as_slice() == splitters
        });
        assert!(splitters.len() >= _SPLITS);

        let mut tree: MaybeUninit<[T; _SPLITS]> = MaybeUninit::uninit();
        flat_tree_index_order(_SPLITS)
            .enumerate()
            .for_each(|(i, j)| unsafe {
                (tree.as_mut_ptr() as *mut T)
                    .add(j)
                    .write(splitters[i].clone())
            });
        let tree = unsafe { tree.assume_init() };

        debug_assert!(tree.structure_check());
        Self { tree }
    }
}

impl<'a, T: 'a + Ord + Clone> KDistribute<T> {
    pub fn into_iter(self) -> impl Iterator<Item = T> + 'a {
        flat_tree_index_order(_SPLITS).map(move |i| self.tree[i].clone())
    }
}

impl<T: Ord> Distribute<T> for KDistribute<T> {
    // Unfortunately, the compiler can not eliminate the branch in the more general version
    // of the r-distribute. Thus a little code duplication is unavoidable.
    fn distribute(&self, el: &T) -> usize {
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

    fn splitter_at(&self, idx: usize) -> &T {
        debug_assert!(idx < self.tree.len());
        let tree_idx = self.tree.select_tree_index(idx);
        self.tree.get(tree_idx)
    }

    fn insert_splitter(&mut self, splitter: T) -> T {
        let result = self.tree.insert_splitter_at_idx(splitter, 0);
        debug_assert!(self.tree.structure_check());
        result
    }

    fn replace_splitter(&mut self, splitter: T, idx: usize) -> T {
        debug_assert!(idx < self.tree.len());
        self.tree.replace_splitter(splitter, idx)
    }

    fn structure_check(&self) -> bool {
        self.tree.structure_check()
    }
}

impl<T: Debug + Ord> Debug for KDistribute<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        (&self.tree as &[T]).fmt(f)
    }
}

impl<T: Ord> TreeBuffer<T, [T]> for SmallVec<[T; 5]> {
    fn len(&self) -> usize {
        self.len()
    }

    fn get_mut(&mut self, index: usize) -> &mut T {
        &mut self[index]
    }

    unsafe fn get_unchecked(&self, index: usize) -> &T {
        self.as_ref().get_unchecked(index)
    }
}

#[derive(Debug)]
pub(crate) struct RDistribute<T: Ord> {
    tree: SmallVec<[T; 5]>,
}

impl<T: Ord> RDistribute<T> {
    pub fn new() -> Self {
        Self {
            tree: SmallVec::new(),
        }
    }
}

impl<T: Ord> Distribute<T> for RDistribute<T> {
    fn distribute(&self, el: &T) -> usize {
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

    fn splitter_at(&self, idx: usize) -> &T {
        debug_assert!(idx < self.tree.len());
        let tree_idx = self.tree.select_tree_index(idx);
        self.tree.get(tree_idx)
    }

    fn insert_splitter(&mut self, splitter: T) -> T {
        if self.tree.len() == 0 {
            return splitter;
        }

        let result = self.tree.insert_splitter_at_idx(splitter, 0);
        debug_assert!(self.tree.structure_check());
        result
    }

    fn replace_splitter(&mut self, splitter: T, idx: usize) -> T {
        debug_assert!(idx < self.tree.len());
        self.tree.replace_splitter(splitter, idx)
    }

    fn structure_check(&self) -> bool {
        self.tree.structure_check()
    }
}

impl<T: Ord + Clone> RDistribute<T> {
    // adds a splitter at the last index by rebuilding the complete tree
    pub fn add_splitter(&mut self, s: T) {
        let mut buffer = SmallVec::<[T; 5]>::new();
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

    pub fn into_vec(self) -> Vec<T> {
        self.data
    }

    /// used for checking invariants
    pub fn min(&self) -> Option<&T> {
        self.data.iter().min()
    }

    /// used for checking invariants
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
    data: ArrayVec<[T; _M]>,
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

    /// used for checking invariants
    pub fn min(&self) -> Option<&T> {
        self.data.iter().min()
    }

    /// used for checking invariants
    pub fn max(&self) -> Option<&T> {
        self.data.iter().max()
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

        assert_eq!(_SPLITS, distr.insert_splitter(_SPLITS));
        assert_eq!(_SPLITS, distr.insert_splitter(0));
        assert_eq!(_SPLITS - 1, distr.insert_splitter(1));
        assert_eq!(_SPLITS - 2, distr.insert_splitter(2));
        assert_eq!(
            _SPLITS - 3,
            distr.replace_splitter(2 * _SPLITS + 3, _SPLITS - 1)
        );
        assert!(distr.structure_check());
        assert_eq!(2 * _SPLITS + 3, distr.insert_splitter(3));
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
}
