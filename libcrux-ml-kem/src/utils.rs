// C extraction:
// A couple helper functions and definitions -- this file ends up being bundled in
// libcrux_core.{c,h}, so if you need something that has to be shared across multiple mlkem
// instances / implementations, it can go in here.

/// Pad the `slice` with `0`s at the end.
#[inline(always)]
#[cfg_attr(hax, hax_lib::requires(
    slice.len() <= LEN
))]
pub(crate) fn into_padded_array<const LEN: usize>(slice: &[u8]) -> [u8; LEN] {
    let mut out = [0u8; LEN];
    out[0..slice.len()].copy_from_slice(slice);
    out
}

// C extraction:
//
// This is only enabled when extracting.
//
// Without these type abbreviations, the monomorphized definitions end up being inserted at the
// first location that they are used, which might be, e.g., the avx2 impl of mlkem512, resulting in
// the portable impl of mlkem512 including the header for the avx2 impl of mlkem512 to have this
// type definition in scope!
//
// To avoid that, we manually place those definitions in this file, which ends up in a shared
// header.
//
// TODO: use proper constants. They don't work right now ...
#[cfg(eurydice)]
mod extraction_helper {
    type Keypair512 = ([u8; 768], [u8; 800]);
    type Keypair768 = ([u8; 1152], [u8; 1184]);
    type Keypair1024 = ([u8; 1536], [u8; 1568]);
}
