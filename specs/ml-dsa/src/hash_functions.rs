/// Hash function wrappers — FIPS 204, Section 3.7.
///
/// H(str, ℓ) = SHAKE256(str, 8ℓ)
/// G(str, ℓ) = SHAKE128(str, 8ℓ)
///
/// All functions are marked opaque for F* extraction since they
/// involve dynamic-length concatenation internally.

/// H: SHAKE256 of a single input, producing N bytes.
#[hax_lib::opaque]
pub(crate) fn h<const N: usize>(input: &[u8]) -> [u8; N] {
    hacspec_sha3::shake256(input)
}

/// G: SHAKE128 of a single input, producing N bytes.
#[hax_lib::opaque]
pub(crate) fn g<const N: usize>(input: &[u8]) -> [u8; N] {
    hacspec_sha3::shake128(input)
}

/// H applied to the concatenation of two byte strings.
#[hax_lib::opaque]
pub(crate) fn h2<const N: usize>(a: &[u8], b: &[u8]) -> [u8; N] {
    let mut input = a.to_vec();
    input.extend_from_slice(b);
    hacspec_sha3::shake256(&input)
}

/// H applied to the concatenation of three byte strings.
#[hax_lib::opaque]
pub(crate) fn h3<const N: usize>(a: &[u8], b: &[u8], c: &[u8]) -> [u8; N] {
    let mut input = a.to_vec();
    input.extend_from_slice(b);
    input.extend_from_slice(c);
    hacspec_sha3::shake256(&input)
}

/// G applied to the concatenation of two byte strings.
#[hax_lib::opaque]
pub(crate) fn g2<const N: usize>(a: &[u8], b: &[u8]) -> [u8; N] {
    let mut input = a.to_vec();
    input.extend_from_slice(b);
    hacspec_sha3::shake128(&input)
}
