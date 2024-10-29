use crate::constants::SHARED_SECRET_SIZE;

// These are crude attempts to prevent LLVM from optimizing away the code in this
// module. This is not guaranteed to work but at the time of writing, achieved
// its goals.
// `read_volatile` could be used as well but seems unnecessary at this point in
// time.
// Examine the output that LLVM produces for this code from time to time to ensure
// operations are not being optimized away/constant-timedness is not being broken.
//
// XXX: We have to disable this for C extraction for now. See eurydice/issues#37

/// Return 1 if `value` is not zero and 0 otherwise.
fn inz(value: u8) -> u8 {
    let value = value as u16;
    let result = ((value | (!value).wrapping_add(1)) >> 8) & 1;
    result as u8
}

#[inline(never)] // Don't inline this to avoid that the compiler optimizes this out.
fn is_non_zero(value: u8) -> u8 {
    #[cfg(eurydice)]
    return inz(value);

    #[cfg(not(eurydice))]
    core::hint::black_box(inz(value))
}

/// Return 1 if the bytes of `lhs` and `rhs` do not exactly
/// match and 0 otherwise.
#[cfg_attr(hax, hax_lib::requires(
    lhs.len() == rhs.len()
))]
fn compare(lhs: &[u8], rhs: &[u8]) -> u8 {
    let mut r: u8 = 0;
    for i in 0..lhs.len() {
        r |= lhs[i] ^ rhs[i];
    }

    is_non_zero(r)
}

/// If `selector` is not zero, return the bytes in `rhs`; return the bytes in
/// `lhs` otherwise.
#[cfg_attr(hax, hax_lib::requires(
    lhs.len() == rhs.len() &&
    lhs.len() == SHARED_SECRET_SIZE
))]
fn select_ct(lhs: &[u8], rhs: &[u8], selector: u8) -> [u8; SHARED_SECRET_SIZE] {
    let mask = is_non_zero(selector).wrapping_sub(1);
    let mut out = [0u8; SHARED_SECRET_SIZE];

    for i in 0..SHARED_SECRET_SIZE {
        out[i] = (lhs[i] & mask) | (rhs[i] & !mask);
    }

    out
}

#[inline(never)] // Don't inline this to avoid that the compiler optimizes this out.
#[cfg_attr(hax, hax_lib::requires(
    lhs.len() == rhs.len()
))]
pub(crate) fn compare_ciphertexts_in_constant_time(lhs: &[u8], rhs: &[u8]) -> u8 {
    #[cfg(eurydice)]
    return compare(lhs, rhs);

    #[cfg(not(eurydice))]
    core::hint::black_box(compare(lhs, rhs))
}

#[inline(never)] // Don't inline this to avoid that the compiler optimizes this out.
#[cfg_attr(hax, hax_lib::requires(
    lhs.len() == rhs.len() &&
    lhs.len() == SHARED_SECRET_SIZE
))]
pub(crate) fn select_shared_secret_in_constant_time(
    lhs: &[u8],
    rhs: &[u8],
    selector: u8,
) -> [u8; SHARED_SECRET_SIZE] {
    #[cfg(eurydice)]
    return select_ct(lhs, rhs, selector);

    #[cfg(not(eurydice))]
    core::hint::black_box(select_ct(lhs, rhs, selector))
}

#[cfg_attr(hax, hax_lib::requires(
    lhs_c.len() == rhs_c.len() &&
    lhs_s.len() == rhs_s.len() &&
    lhs_s.len() == SHARED_SECRET_SIZE
))]
pub(crate) fn compare_ciphertexts_select_shared_secret_in_constant_time(
    lhs_c: &[u8],
    rhs_c: &[u8],
    lhs_s: &[u8],
    rhs_s: &[u8],
) -> [u8; SHARED_SECRET_SIZE] {
    let selector = compare_ciphertexts_in_constant_time(lhs_c, rhs_c);

    select_shared_secret_in_constant_time(lhs_s, rhs_s, selector)
}
