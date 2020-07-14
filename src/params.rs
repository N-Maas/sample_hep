/// Tuning parameters
// TODO: currently at most 32 possible for _K due to array limitations
pub const _K: usize = 32;
pub const _M: usize = 256;

const_assert!(_K.is_power_of_two());
