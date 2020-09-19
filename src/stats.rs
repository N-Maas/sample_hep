use num_format::{Locale, ToFormattedString};
use std::{
    sync::atomic::{AtomicU64, Ordering},
    time::Instant,
};

pub static TOTAL_TIME: AtomicU64 = AtomicU64::new(0);
pub static PUSH_TIME: AtomicU64 = AtomicU64::new(0);
pub static POP_TIME: AtomicU64 = AtomicU64::new(0);
pub static LOOP_TIME: AtomicU64 = AtomicU64::new(0);
pub static DEL_OVERFLOW_TIME: AtomicU64 = AtomicU64::new(0);
pub static GROUP_OVERFLOW_TIME: AtomicU64 = AtomicU64::new(0);
pub static SCAN_AND_SPLIT_TIME: AtomicU64 = AtomicU64::new(0);
pub static REFILL_GROUP_TIME: AtomicU64 = AtomicU64::new(0);
pub static REFILL_TIME: AtomicU64 = AtomicU64::new(0);

pub static PULL_COUNTER: AtomicU64 = AtomicU64::new(0);
pub static PULL_OVERFLOW_COUNTER: AtomicU64 = AtomicU64::new(0);

pub fn reset_stats() {
    TOTAL_TIME.store(0, Ordering::Relaxed);
    PUSH_TIME.store(0, Ordering::Relaxed);
    POP_TIME.store(0, Ordering::Relaxed);
    LOOP_TIME.store(0, Ordering::Relaxed);
    DEL_OVERFLOW_TIME.store(0, Ordering::Relaxed);
    GROUP_OVERFLOW_TIME.store(0, Ordering::Relaxed);
    SCAN_AND_SPLIT_TIME.store(0, Ordering::Relaxed);
    REFILL_GROUP_TIME.store(0, Ordering::Relaxed);
    REFILL_TIME.store(0, Ordering::Relaxed);

    PULL_COUNTER.store(0, Ordering::Relaxed);
    PULL_OVERFLOW_COUNTER.store(0, Ordering::Relaxed);
}

pub fn print_stats() {
    println!("");
    println!("TIMINGS");
    println!(
        "total = {:>15}",
        TOTAL_TIME
            .load(Ordering::Relaxed)
            .to_formatted_string(&Locale::de)
    );
    println!(
        "push  = {:>15} ---     loop     = {:>15} - del_overflow = {:>15} - group_overflow = {:>15}",
        PUSH_TIME.load(Ordering::Relaxed).to_formatted_string(&Locale::de),
        LOOP_TIME.load(Ordering::Relaxed).to_formatted_string(&Locale::de),
        DEL_OVERFLOW_TIME.load(Ordering::Relaxed).to_formatted_string(&Locale::de),
        GROUP_OVERFLOW_TIME.load(Ordering::Relaxed).to_formatted_string(&Locale::de),
    );
    println!(
        "pop   = {:>15} --- refill_total = {:>15} - refill_group = {:>15} - scan_and_split = {:>15}",
        POP_TIME.load(Ordering::Relaxed).to_formatted_string(&Locale::de),
        REFILL_TIME.load(Ordering::Relaxed).to_formatted_string(&Locale::de),
        REFILL_GROUP_TIME.load(Ordering::Relaxed).to_formatted_string(&Locale::de),
        SCAN_AND_SPLIT_TIME.load(Ordering::Relaxed).to_formatted_string(&Locale::de),
    );
    println!("COUNTERS");
    println!(
        "pulls = {} - pull_overflows = {}",
        PULL_COUNTER
            .load(Ordering::Relaxed)
            .to_formatted_string(&Locale::de),
        PULL_OVERFLOW_COUNTER
            .load(Ordering::Relaxed)
            .to_formatted_string(&Locale::de),
    );
    println!("");
}

pub fn add_time(time: Instant, counter: &AtomicU64) {
    counter.fetch_add(time.elapsed().as_nanos() as u64, Ordering::Relaxed);
}

pub fn count(counter: &AtomicU64) {
    counter.fetch_add(1, Ordering::Relaxed);
}
