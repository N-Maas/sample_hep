use crate::params::*;

use smallvec::{smallvec, SmallVec};
use std::convert::{AsMut, AsRef};
use std::marker::PhantomData;
use std::{mem, ops::IndexMut};

const _SPLITS: usize = _K - 1;

// ----- traits ----- //

pub trait Distribute<T: Ord> {
    fn distribute(&self, el: &T) -> usize;

    fn insert_splitter(&mut self, splitter: T) -> T;
}

enum TreeElement {
    Node(usize, usize),
    UnaryNode(usize),
    Leaf,
}

// helper trait for common functionality of R-way and k-way distribute
trait TreeBuffer<T: Ord, R: ?Sized>: AsRef<R> + AsMut<R>
where
    R: IndexMut<usize, Output = T>,
{
    fn len(&self) -> usize;

    unsafe fn get_unchecked(&self, index: usize) -> &T;

    fn element_type(&self, index: usize) -> TreeElement {
        let high = self.len() / 2;
        let low = (self.len() - 1) / 2;

        match index {
            i if i < low => TreeElement::Node(2 * i + 1, 2 * i + 2),
            i if i < high => TreeElement::UnaryNode(2 * i + 1),
            i if i < self.len() => TreeElement::Leaf,
            i => panic!("Invalid index: {:?}", i),
        }
    }

    /// debugging
    fn structure_check(&self) -> bool {
        let self_r = self.as_ref();
        let mut el_type = 0;

        (0..self.len())
            .map(|i| match self.element_type(i) {
                TreeElement::Node(left, right) => {
                    self_r[left] <= self_r[i] && self_r[i] <= self_r[right] && el_type == 0
                }
                TreeElement::UnaryNode(left) => {
                    let res = self_r[left] <= self_r[i] && el_type <= 1;
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
        let el_type = self.element_type(idx);

        if splitter < self.as_ref()[idx] {
            match el_type {
                TreeElement::Leaf => mem::replace(&mut self.as_mut()[idx], splitter),
                TreeElement::UnaryNode(left) | TreeElement::Node(left, _) => {
                    let new = self.insert_splitter_at_idx(splitter, left);
                    let old = mem::replace(&mut self.as_mut()[idx], new);

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

    fn traverse_in_order(&self) -> TreeIter<'_, Self, T, R> {
        TreeIter {
            tree: self,
            stack: if self.len() > 0 {
                smallvec![(0, DFSLabel::from(self.element_type(0)))]
            } else {
                SmallVec::new()
            },
            _t: PhantomData,
            _r: PhantomData,
        }
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

struct TreeIter<'a, B: ?Sized, T: Ord, R: ?Sized + IndexMut<usize, Output = T>>
where
    B: TreeBuffer<T, R> + AsRef<R> + AsMut<R>,
{
    tree: &'a B,
    // the TreeElement enum might be a bit misused here
    stack: SmallVec<[(usize, DFSLabel); _SPLITS.count_ones() as usize]>,
    _t: PhantomData<T>,
    _r: PhantomData<R>,
}

impl<'a, B, T: Ord + 'a, R: ?Sized + IndexMut<usize, Output = T>> Iterator for TreeIter<'a, B, T, R>
where
    B: TreeBuffer<T, R> + AsRef<R> + AsMut<R>,
{
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (i, state) = self.stack.pop()?;

            match state {
                DFSLabel::Both(left, right) => {
                    self.stack.push((i, DFSLabel::Right(right)));
                    self.stack
                        .push((left, DFSLabel::from(self.tree.element_type(left))));
                }
                DFSLabel::Left(left) => {
                    self.stack.push((i, DFSLabel::None));
                    self.stack
                        .push((left, DFSLabel::from(self.tree.element_type(left))));
                }
                DFSLabel::Right(right) => {
                    self.stack
                        .push((right, DFSLabel::from(self.tree.element_type(right))));
                    return Some(i);
                }
                DFSLabel::None => return Some(i),
            }
            debug_assert!(!self.stack.spilled());
        }
    }
}

impl<T: Ord> TreeBuffer<T, [T]> for [T; _SPLITS] {
    fn len(&self) -> usize {
        _SPLITS
    }

    unsafe fn get_unchecked(&self, index: usize) -> &T {
        self.as_ref().get_unchecked(index)
    }
}

#[derive(Debug)]
pub struct KDistribute<T: Ord> {
    tree: [T; _SPLITS],
}

// TODO: default unnecessary
impl<T: Ord + Clone + Default> KDistribute<T> {
    pub fn new(splitters: &[T]) -> Self {
        debug_assert!({
            let mut vec = splitters.to_owned();
            vec.sort();
            vec.as_slice() == splitters
        });
        assert!(splitters.len() >= _SPLITS);

        let mut tree: [T; _SPLITS] = Default::default();
        tree.traverse_in_order()
            .collect::<Vec<usize>>()
            .into_iter()
            .enumerate()
            .for_each(|(i, j)| tree[j] = splitters[i].clone());

        debug_assert!(tree.structure_check());
        Self { tree }
    }
}

impl<T: Ord> Distribute<T> for KDistribute<T> {
    fn distribute(&self, el: &T) -> usize {
        let mut idx = 0;
        for _ in 0..(_SPLITS.count_ones()) {
            debug_assert!(idx < self.tree.len());

            // compiler seems unable to completely remove bound checks
            let is_less = unsafe { el < self.tree.get_unchecked(idx) };
            idx = 2 * idx + (if is_less { 1 } else { 2 });
        }

        debug_assert!(
            idx >= _SPLITS && idx < 2 * _SPLITS + 1,
            "Invalid result: {:?}",
            idx
        );
        idx - _SPLITS
    }

    fn insert_splitter(&mut self, splitter: T) -> T {
        let result = self.tree.insert_splitter_at_idx(splitter, 0);
        debug_assert!(self.tree.structure_check());
        result
    }
}

impl<T: Ord> TreeBuffer<T, [T]> for SmallVec<[T; 5]> {
    fn len(&self) -> usize {
        self.len()
    }

    unsafe fn get_unchecked(&self, index: usize) -> &T {
        self.as_ref().get_unchecked(index)
    }
}
#[derive(Debug)]
pub struct RDistribute<T: Ord> {
    tree: SmallVec<[T; 5]>,
}

impl<T: Ord> RDistribute<T> {
    pub fn new() -> Self {
        Self {
            tree: SmallVec::new(),
        }
    }
}

#[test]
fn basic() {
    use std::iter::FromIterator;

    let splitters = &Vec::from_iter(1.._K);
    let distr = KDistribute::<usize>::new(splitters);

    for i in 0.._K {
        assert_eq!(i, distr.distribute(&i));
    }
}

#[test]
fn move_subtree() {
    use std::iter::FromIterator;

    let splitters = &Vec::from_iter(1.._K);
    let mut distr = KDistribute::<usize>::new(splitters);

    assert_eq!(31, distr.insert_splitter(31));
    assert_eq!(31, distr.insert_splitter(0));
    assert_eq!(30, distr.insert_splitter(10));
    assert_eq!(29, distr.insert_splitter(15));
    assert_eq!(28, distr.insert_splitter(26));
}
