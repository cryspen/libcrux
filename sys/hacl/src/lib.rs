//! # HACL Sys
//!
//! Bindings to HACL C code
#![no_std]
#![allow(non_camel_case_types, non_snake_case)]

mod bindings;
pub use bindings::*;

#[cfg(test)]
mod tests {
    #[test]
    fn spot() {
        unsafe {
            let input = b"hash input";
            let mut digest = [0u8; 32];
            crate::Hacl_Hash_SHA2_hash_256(
                input.as_ptr() as _,
                input.len() as u32,
                digest.as_mut_ptr(),
            );
            assert_eq!(
                "35f1be59fa32bb37e2aea1ca1844d56a5bfc8a17851b40933045db837df8e7f1",
                hex::encode(&digest)
            );
        }
    }
}
