/// Tuning parameters
pub const _K: usize = 128;
pub const _M: usize = 256;

pub const _SCALING: usize = _K / 2;
pub const _SAMPLING: usize = 5;

const_assert!(_K.is_power_of_two());
const_assert!(_SAMPLING % 2 == 1);
