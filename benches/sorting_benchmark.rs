#[macro_use]
extern crate lazy_static;

use criterion::{criterion_group, criterion_main, Criterion, Throughput};
use rand::{Rng, SeedableRng};
use rand_pcg::Pcg32;
use sample_heap::SampleHeap;
use std::{cmp::Reverse, collections::BinaryHeap, fmt::Debug};

fn random_sequence(len: usize, range: u32, seed: [u8; 16]) -> Vec<u32> {
    let mut rng = Pcg32::from_seed(seed);
    let mut result = Vec::with_capacity(len);
    for _ in 0..len {
        result.push(rng.gen_range(0, range));
    }
    result
}

fn heap_sort(input: &Vec<u32>) -> Vec<u32> {
    let mut heap = SampleHeap::new();
    let mut result = Vec::with_capacity(input.len());
    for val in input {
        heap.push(*val);
    }
    while let Some(el) = heap.pop() {
        result.push(el);
    }
    result
}

fn bheap_sort(input: &Vec<u32>) -> Vec<u32> {
    let mut heap: BinaryHeap<Reverse<u32>> = BinaryHeap::new();
    let mut result = Vec::with_capacity(input.len());
    for val in input {
        heap.push(Reverse(*val));
    }
    while let Some(Reverse(el)) = heap.pop() {
        result.push(el);
    }
    result
}

fn q_sort(input: &Vec<u32>) -> Vec<u32> {
    let mut result = input.clone();
    result.sort();
    result
}

fn assert_vecs_eq<T: PartialEq + Debug>(left: &Vec<T>, right: &Vec<T>) {
    assert_eq!(left.len(), right.len());
    left.iter()
        .zip(right.iter())
        .for_each(|(l, r)| assert_eq!(l, r));
}

// small benchmark with (relatively) unique values

lazy_static! {
    static ref SMALL_INPUT: Vec<u32> = random_sequence(1000, u32::MAX, [0; 16]);
    static ref SMALL_SORTED: Vec<u32> = {
        let mut data = SMALL_INPUT.clone();
        data.sort();
        data
    };
}

fn small_benchmark(c: &mut Criterion) {
    c.bench_function("heap sort 1000", |b| {
        b.iter(|| assert_vecs_eq(&heap_sort(&SMALL_INPUT), &SMALL_SORTED))
    });
    c.bench_function("binary heap sort 1000", |b| {
        b.iter(|| assert_vecs_eq(&bheap_sort(&SMALL_INPUT), &SMALL_SORTED))
    });
    c.bench_function("quicksort 1000", |b| {
        b.iter(|| assert_vecs_eq(&q_sort(&SMALL_INPUT), &SMALL_SORTED))
    });
}

// benchmark with (relatively) unique values, using the capacity of the first group

lazy_static! {
    static ref BASE_INPUT: Vec<u32> = random_sequence(15000, u32::MAX, [1; 16]);
    static ref BASE_SORTED: Vec<u32> = {
        let mut data = BASE_INPUT.clone();
        data.sort();
        data
    };
}

fn base_benchmark(c: &mut Criterion) {
    c.bench_function("heap sort 15000", |b| {
        b.iter(|| assert_vecs_eq(&heap_sort(&BASE_INPUT), &BASE_SORTED))
    });
    c.bench_function("binary heap sort 15000", |b| {
        b.iter(|| assert_vecs_eq(&bheap_sort(&BASE_INPUT), &BASE_SORTED))
    });
    c.bench_function("quicksort 15000", |b| {
        b.iter(|| assert_vecs_eq(&q_sort(&BASE_INPUT), &BASE_SORTED))
    });
}

// larger benchmark with (relatively) unique values

fn extended_medium_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("Heap sort: medium size benchmarks");
    group.sample_size(20);

    for size in &[500_000, 1_000_000, 1_500_000, 2_000_000] {
        group.throughput(Throughput::Bytes(4 * *size as u64));
        for seed in 0..4 {
            let input = random_sequence(*size, u32::MAX, [seed; 16]);
            let mut sorted = input.clone();
            sorted.sort();
            group.bench_with_input(
                format!("size={}, seed={}", size, seed),
                &(&input, &sorted),
                |b, &(input, sorted)| b.iter(|| assert_vecs_eq(&heap_sort(input), sorted)),
            );
        }
    }
}

// larger benchmark with (relatively) unique values

fn extended_medium_benchmark_bheap(c: &mut Criterion) {
    let mut group = c.benchmark_group("Heap sort: medium size benchmarks");
    group.sample_size(20);

    for size in &[500_000, 1_000_000, 1_500_000, 2_000_000] {
        group.throughput(Throughput::Bytes(4 * *size as u64));
        for seed in 0..4 {
            let input = random_sequence(*size, u32::MAX, [seed; 16]);
            let mut sorted = input.clone();
            sorted.sort();
            group.bench_with_input(
                format!("size={}, seed={}", size, seed),
                &(&input, &sorted),
                |b, &(input, sorted)| b.iter(|| assert_vecs_eq(&bheap_sort(input), sorted)),
            );
        }
    }
}

criterion_group!(small, small_benchmark, base_benchmark);
criterion_group!(medium, extended_medium_benchmark);
criterion_group!(medium_bheap, extended_medium_benchmark_bheap);
criterion_main!(medium);
