// TODO clean conditional compilation solution
/// Tuning parameters
#[cfg(test)]
pub const _K: usize = 8;
#[cfg(not(test))]
pub const _K: usize = 64;
#[cfg(test)]
pub const _M: usize = 16;
#[cfg(not(test))]
pub const _M: usize = 256;
#[cfg(test)]
pub const _BUFFER_SIZE: usize = 32;
#[cfg(not(test))]
pub const _BUFFER_SIZE: usize = 1024;

pub const _SCALING: usize = _K / 2;
pub const _SAMPLING_SIZE: usize = 3;
pub const _SAMPLING_COUNT: usize = 3;

const_assert!(_K.is_power_of_two());
const_assert!((_SAMPLING_SIZE * _SAMPLING_COUNT) % 2 == 1);

/// macro similar to debug_assert! using conditional compilation
#[macro_export]
macro_rules! dbg_assertion {
    ( $x:expr ) => {
        // #[cfg(any(debug, test))]
        debug_assert!($x);
    };
}
