use crate::kem::kyber768::{CIPHERTEXT_SIZE, SHARED_SECRET_SIZE};

// TODO: Attribute this to RustCrypto
#[inline]
fn is_non_zero(value: u8) -> u8 {
    const SHIFT_BITS: usize = core::mem::size_of::<u64>() - 1;
    let value = value as u64;

    (((value | (!value).wrapping_add(1)) >> SHIFT_BITS) & 1) as u8
}

pub(crate) fn compare_ciphertexts_in_constant_time(lhs: &[u8], rhs: &[u8]) -> u8 {
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
