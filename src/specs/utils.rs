//! hacspec utilities to convert types etc.

use hacspec_lib::prelude::*;

/// Convert a hacspec [`Seq`] into a Rust `Vec`.
pub fn seq_to_vec(seq: Seq<U8>) -> Vec<u8> {
    seq.into_native()
}

pub fn vec_to_seq(vec: Vec<u8>) -> Seq<U8> {
    Seq::<U8>::from_public_slice(&vec)
}

#[cfg_attr(feature = "use_attributes", not_hacspec)]
pub fn hex_string_to_bytes(s: &str) -> Vec<u8> {
    debug_assert!(s.len() % 2 == 0);
    let b: Result<Vec<u8>, ParseIntError> = (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16))
        .collect();
    b.expect("Error parsing hex string")
}
