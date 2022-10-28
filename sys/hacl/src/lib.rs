//! # HACL Sys
//!
//! Bindings to HACL C code

#![allow(non_camel_case_types, non_snake_case)]

mod bindings;
pub use bindings::*;

// We need to have some dummy functions to make the linker happy.

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64")))]
pub unsafe fn Hacl_Chacha20Poly1305_128_aead_encrypt(
    _k: *mut u8,
    _n: *mut u8,
    _aadlen: u32,
    _aad: *mut u8,
    _mlen: u32,
    _m: *mut u8,
    _cipher: *mut u8,
    _mac: *mut u8,
) {
}
#[cfg(not(any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64")))]
pub unsafe fn Hacl_Chacha20Poly1305_128_aead_decrypt(
    _k: *mut u8,
    _n: *mut u8,
    _aadlen: u32,
    _aad: *mut u8,
    _mlen: u32,
    _m: *mut u8,
    _cipher: *mut u8,
    _mac: *mut u8,
) -> u32 {
    1
}

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
pub unsafe fn Hacl_Chacha20Poly1305_256_aead_encrypt(
    _k: *mut u8,
    _n: *mut u8,
    _aadlen: u32,
    _aad: *mut u8,
    _mlen: u32,
    _m: *mut u8,
    _cipher: *mut u8,
    _mac: *mut u8,
) {
}
#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
pub unsafe fn Hacl_Chacha20Poly1305_256_aead_decrypt(
    _k: *mut u8,
    _n: *mut u8,
    _aadlen: u32,
    _aad: *mut u8,
    _mlen: u32,
    _m: *mut u8,
    _cipher: *mut u8,
    _mac: *mut u8,
) -> u32 {
    1
}
