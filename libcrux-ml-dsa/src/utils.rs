/// Pad the `slice` with `0`s at the end.
#[inline(always)]
pub(crate) fn into_padded_array<const LEN: usize>(slice: &[u8]) -> [u8; LEN] {
    debug_assert!(slice.len() <= LEN);
    let mut out = [0u8; LEN];
    out[0..slice.len()].copy_from_slice(slice);
    out
}
