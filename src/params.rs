/// Tuning parameters
// TODO: currently at most 32 possible due to array limitations
pub const _K: usize = 32;

const_assert!(_K.is_power_of_two());
