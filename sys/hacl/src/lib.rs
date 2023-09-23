//! # HACL Sys
//!
//! Bindings to HACL C code

#![allow(non_camel_case_types, non_snake_case, non_upper_case_globals)]

#[cfg(not(target_arch = "wasm32"))]
mod bindings;
#[cfg(not(target_arch = "wasm32"))]
pub use bindings::*;

#[cfg(target_arch = "wasm32")]
mod wasm32_bindings;
#[cfg(target_arch = "wasm32")]
pub use wasm32_bindings::*;

/// Free a raw C pointer.
pub unsafe fn cfree_u64(p: *mut u64) {
    libc::free(p as *mut libc::c_void);
}

#[cfg(test)]
mod test {
    use crate::*;

    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
    #[cfg_attr(not(target_arch = "wasm32"), test)]
    fn poc() {
        let mut digest = [0u8; 32];
        let msg = b"libcrux sha2 256 tests";
        unsafe {
            Hacl_Streaming_SHA2_hash_256(msg.as_ptr() as _, msg.len() as u32, digest.as_mut_ptr());
        }
        let expected = "8683520e19e5b33db33c8fb90918c0c96fcdfd9a17c695ce0f0ea2eaa0c95956";
        assert_eq!(hex::encode(digest), expected);
    }
}
