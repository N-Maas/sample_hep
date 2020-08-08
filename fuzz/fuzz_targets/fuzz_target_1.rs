#![no_main]
use std::collections::BinaryHeap;
use std::cmp::Reverse;
use libfuzzer_sys::fuzz_target;
use sample_heap::SampleHeap;

fuzz_target!(|elements: Vec<Option<u8>>| {
    let mut heap = SampleHeap::new();
    let mut bin_heap: BinaryHeap<Reverse<u8>> = BinaryHeap::new();
    
    for el in elements {
        match el {
            Some(val) => {
                dbg!(val);
                heap.push(val);
                bin_heap.push(Reverse(val));
            }
            None => {
                assert_eq!(heap.pop(), bin_heap.pop().map(|Reverse(x)| x));
            }
        }
    }
    while let Some(val) = heap.pop() {
        assert_eq!(Some(val), bin_heap.pop().map(|Reverse(x)| x));
    }
    assert!(heap.is_empty());
    assert!(bin_heap.is_empty());
});
