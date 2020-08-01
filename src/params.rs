/// Tuning parameters
pub const _K: usize = 128;
pub const _M: usize = 256;

pub const _SCALING: usize = _K / 2;
pub const _SAMPLING: usize = 8;

const_assert!(_K.is_power_of_two());
