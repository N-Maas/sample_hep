use crate::params::*;

use std::cmp::Ordering;
use std::mem;

const _SPLITS: usize = _K - 1;

#[derive(Debug)]
pub struct KDistribute<T: Ord + Clone> {
    tree: [T; _K - 1],
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

        let mut distribute = Self {
            tree: Default::default(),
        };
        Self::set_tree_val(&mut distribute.tree, 0, splitters);

        debug_assert!(distribute.structure_check());
        distribute
    }

    fn set_tree_val(tree: &mut [T; _K - 1], idx: usize, splitters: &[T]) {
        debug_assert!(idx < _SPLITS);
        debug_assert!((splitters.len() + 1).is_power_of_two());

        let mid = splitters.len() >> 1;
        tree[idx] = splitters[mid].clone();

        if splitters.len() > 1 {
            Self::set_tree_val(tree, 2 * idx + 1, &splitters[0..mid]);
            Self::set_tree_val(tree, 2 * idx + 2, &splitters[(mid + 1)..splitters.len()]);
        }
    }

    pub fn distribute(&self, el: &T) -> usize {
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

    pub fn insert_splitter(&mut self, splitter: T) -> T {
        let result = self.insert_splitter_at_idx(splitter, 0);
        debug_assert!(self.structure_check());
        result
    }

    /// Inserts the splitter at the appropriate position, moving the remaining splitters to the right and returning the largest one.
    fn insert_splitter_at_idx(&mut self, splitter: T, idx: usize) -> T {
        let is_leaf = idx >= (_SPLITS >> 1);

        match (is_leaf, splitter < self.tree[idx]) {
            (true, false) => splitter,
            (true, true) => mem::replace(&mut self.tree[idx], splitter),
            (false, false) => self.insert_splitter_at_idx(splitter, 2 * idx + 2),
            (false, true) => {
                let new = self.insert_splitter_at_idx(splitter, 2 * idx + 1);
                let old = mem::replace(&mut self.tree[idx], new);
                // causes unnecessary comparisons
                self.insert_splitter_at_idx(old, 2 * idx + 2)
            }
        }
    }

    /// for debugging
    fn structure_check(&self) -> bool {
        (0..(_SPLITS >> 1))
            .map(|i| self.tree[2 * i + 1] <= self.tree[i] && self.tree[i] <= self.tree[2 * i + 2])
            .find(|x| !x)
            .is_none()
    }
}

#[test]
fn basic() {
    use std::iter::FromIterator;

    let mut start = 0;
    let splitters = &Vec::from_iter(std::iter::from_fn(|| {
        start += 1;
        Some(start).filter(|x| *x < _K)
    }));
    let distr = KDistribute::<usize>::new(splitters);

    for i in 0.._K {
        assert_eq!(i, distr.distribute(&i));
    }
}

#[test]
fn move_subtree() {
    use std::iter::FromIterator;

    let mut start = 0;
    let splitters = &Vec::from_iter(std::iter::from_fn(|| {
        start += 1;
        Some(start).filter(|x| *x < _K)
    }));
    let mut distr = KDistribute::<usize>::new(splitters);

    assert_eq!(31, distr.insert_splitter(31));
    assert_eq!(31, distr.insert_splitter(0));
    assert_eq!(30, distr.insert_splitter(10));
    assert_eq!(29, distr.insert_splitter(15));
    assert_eq!(28, distr.insert_splitter(26));
}
