use super::constants::SHARED_SECRET_SIZE;
use crate::hax_utils::hax_debug_assert;

// Examine the output that LLVM produces for this code from time to time to ensure
// operations are not being optimized away/constant-timedness is not being broken.

/// Return 1 if `value` is not zero and 0 otherwise.
#[cfg_attr(hax, hax_lib::ensures(|result|
    hax_lib::implies(value == 0, || result == 0) &&
    hax_lib::implies(value != 0, || result == 1)
))]
#[inline(never)] // Don't inline this to avoid that the compiler optimizes this out.
fn is_non_zero(value: u8) -> u8 {
    let value = value as u16;

    let result = ((value | (!value).wrapping_add(1)) >> 8) & 1;

    result as u8
}

/// Return 1 if the bytes of `lhs` and `rhs` do not exactly
/// match and 0 otherwise.
#[cfg_attr(hax, hax_lib::ensures(|result|
    hax_lib::implies(lhs == rhs, || result == 0) &&
    hax_lib::implies(lhs != rhs, || result == 1)
))]
pub(crate) fn compare_ciphertexts_in_constant_time<const CIPHERTEXT_SIZE: usize>(
    lhs: &[u8],
    rhs: &[u8],
) -> u8 {
    hax_debug_assert!(lhs.len() == rhs.len());
    hax_debug_assert!(lhs.len() == CIPHERTEXT_SIZE);

    let mut r: u8 = 0;
    for i in 0..CIPHERTEXT_SIZE {
        r |= lhs[i] ^ rhs[i];
    }

    is_non_zero(r)
}

/// If `selector` is not zero, return the bytes in `rhs`; return the bytes in
/// `lhs` otherwise.
#[cfg_attr(hax, hax_lib::ensures(|result|
    hax_lib::implies(selector == 0, || result == lhs) &&
    hax_lib::implies(selector != 0, || result == rhs)
))]
pub(crate) fn select_shared_secret_in_constant_time(
    lhs: &[u8],
    rhs: &[u8],
    selector: u8,
) -> [u8; SHARED_SECRET_SIZE] {
    hax_debug_assert!(lhs.len() == rhs.len());
    hax_debug_assert!(lhs.len() == SHARED_SECRET_SIZE);

    let mask = is_non_zero(selector).wrapping_sub(1);
    let mut out = [0u8; SHARED_SECRET_SIZE];

    for i in 0..SHARED_SECRET_SIZE {
        out[i] = (lhs[i] & mask) | (rhs[i] & !mask);
    }

    out
}
