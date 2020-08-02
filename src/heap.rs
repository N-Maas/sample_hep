use crate::groups::*;
use crate::params::*;
use crate::primitives::*;
use smallvec::SmallVec;
use std::iter;

// TODO: implement Clone?
#[derive(Debug)]
pub struct SampleHeap<T: Ord + Clone> {
    insertion_heap: BufferHeap<T>,
    groups: Groups<T>,
}

impl<T: Ord + Clone> SampleHeap<T> {
    pub fn new() -> Self {
        Self {
            insertion_heap: BufferHeap::new(),
            groups: Groups {
                r_distr: RDistribute::new(),
                deletion_heap: BufferHeap::new(),
                group_list: SmallVec::new(),
            },
        }
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

        if remove_from_del_heap {
            self.groups.deletion_heap.pop()
        } else {
            self.insertion_heap.pop()
        }
    }

    pub fn push(&mut self, el: T) {
        self.insertion_heap
            .push(el)
            .unwrap_or_else(|HeapOverflowError(remaining)| {
                let iter = self.insertion_heap.drain().chain(iter::once(remaining));
                self.groups.insert_all(iter);
            })
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
                let group = self.group_list[idx].as_mut();
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
            let step = _M as f64 / (_K + 1) as f64;
            let first = step.round() as usize - 1;
            let splitters: Vec<T> = (2..=_K)
                .map(|i| elements[(i as f64 * step).round() as usize - 1].clone())
                .collect();
            let mut base_group = BaseGroup::new(max_seq_len, &splitters);
            base_group.forced_insert_all(elements.drain((first + 1)..elements.len()));
            self.group_list
                .push(Box::new(BufferedGroup::from_base_group(base_group)));

            let splitter = elements[first].clone();
            self.r_distr.insert_splitter(splitter);
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
    }

    fn handle_group_overflow(&mut self, group_idx: usize, seq_idx: usize) {
        todo!();
    }

    fn init_group_from(max_seq_len: usize, elements: Vec<T>) -> BaseGroup<T> {
        todo!();
    }
}
