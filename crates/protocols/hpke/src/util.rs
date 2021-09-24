use rand::{rngs::OsRng, RngCore};

#[inline]
pub(crate) fn random(l: usize) -> Vec<u8> {
    // TODO: This function must be replaced with a proper PRNG call.
    debug_assert!(
        l < 128,
        "We only want to take a little bit of randomness here."
    );
    let mut out = vec![0u8; l];
    OsRng.fill_bytes(&mut out);
    out
}

#[inline]
pub(crate) fn concat(values: &[&[u8]]) -> Vec<u8> {
    values.join(&[][..])
}

#[inline]
pub(crate) fn xor_bytes(a: &[u8], b: &[u8]) -> Vec<u8> {
    assert_eq!(a.len(), b.len());
    a.iter().zip(b).map(|(x, y)| x ^ y).collect()
}

#[test]
fn test_concat() {
    let a = "blabla";
    let b = "RFCXXXX ";
    let expected = "blablaRFCXXXX ";
    assert_eq!(
        expected.as_bytes()[..],
        concat(&[&a.as_bytes(), &b.as_bytes()])[..]
    )
}
