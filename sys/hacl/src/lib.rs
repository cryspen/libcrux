//! # HACL Sys
//!
//! Bindings to HACL C code

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
            eprintln!("digest: {:x?}", digest);
        }
    }
}
