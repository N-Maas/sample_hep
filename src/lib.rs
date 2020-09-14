#![feature(new_uninit)]

#[macro_use]
extern crate static_assertions;
#[macro_use]
extern crate lazy_static;

mod groups;
mod params;
mod primitives;

pub mod heap;
pub use heap::SampleHeap;
