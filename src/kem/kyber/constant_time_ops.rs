use super::parameters::SHARED_SECRET_SIZE;

// TODO: Examine the output that LLVM produces for this code to ensure
// operations are not being optimized away/constant-timedness is not being broken.

#[inline]
fn is_non_zero(value: u8) -> u8 {
    let value_negated = -(value as i8);
    ((value | (value_negated as u8)) >> 7) & 1
}

pub(crate) fn compare_ciphertexts_in_constant_time<const CIPHERTEXT_SIZE: usize>(
    lhs: &[u8],
    rhs: &[u8],
) -> u8 {
    debug_assert_eq!(lhs.len(), rhs.len());
    debug_assert_eq!(lhs.len(), CIPHERTEXT_SIZE);

    let mut r: u8 = 0;
    for i in 0..CIPHERTEXT_SIZE {
        r |= lhs[i] ^ rhs[i];
    }

    is_non_zero(r)
}

// Select |lhs| if |selector| == 0, |rhs| otherwise.
pub(crate) fn select_shared_secret_in_constant_time(
    lhs: &[u8],
    rhs: &[u8],
    selector: u8,
) -> [u8; SHARED_SECRET_SIZE] {
    debug_assert_eq!(lhs.len(), rhs.len());
    debug_assert_eq!(lhs.len(), SHARED_SECRET_SIZE);

    let mask = is_non_zero(selector).wrapping_sub(1);
    let mut out = [0u8; SHARED_SECRET_SIZE];

    for i in 0..SHARED_SECRET_SIZE {
        out[i] |= (lhs[i] & mask) | (rhs[i] & !mask);
    }

    out
}
