//! # HACL
//!
//! Interface to call into HACL functions.

mod hw_detection;

use libcrux_hacl::*;

use crate::aead::{Chacha20Key, Iv, Tag};

use self::hw_detection::{simd128_support, simd256_support};

pub(crate) struct ChaCha20Poly1305 {}

impl ChaCha20Poly1305 {
    /// Encrypt
    /// Returns `tag`
    pub(crate) fn encrypt(key: &Chacha20Key, msg_ctxt: &mut [u8], iv: &Iv, aad: &[u8]) -> Tag {
        let mut tag = Tag::default();
        if simd256_support() {
            unsafe {
                Hacl_Chacha20Poly1305_256_aead_encrypt(
                    key.as_ptr() as _,
                    iv.as_ptr() as _,
                    aad.len() as u32,
                    aad.as_ptr() as _,
                    msg_ctxt.len() as u32,
                    msg_ctxt.as_ptr() as _,
                    msg_ctxt.as_mut_ptr(),
                    tag.as_mut_ptr(),
                );
            }
        } else if simd128_support() {
            unsafe {
                Hacl_Chacha20Poly1305_128_aead_encrypt(
                    key.as_ptr() as _,
                    iv.as_ptr() as _,
                    aad.len() as u32,
                    aad.as_ptr() as _,
                    msg_ctxt.len() as u32,
                    msg_ctxt.as_ptr() as _,
                    msg_ctxt.as_mut_ptr(),
                    tag.as_mut_ptr(),
                );
            }
        } else {
            unsafe {
                Hacl_Chacha20Poly1305_32_aead_encrypt(
                    key.as_ptr() as _,
                    iv.as_ptr() as _,
                    aad.len() as u32,
                    aad.as_ptr() as _,
                    msg_ctxt.len() as u32,
                    msg_ctxt.as_ptr() as _,
                    msg_ctxt.as_mut_ptr(),
                    tag.as_mut_ptr(),
                );
            }
        }
        tag
    }

    /// Decrypt
    /// Returns error or `()`.
    pub(crate) fn decrypt(
        key: &Chacha20Key,
        ctxt_msg: &mut [u8],
        iv: &Iv,
        aad: &[u8],
        tag: &Tag,
    ) -> Result<(), &'static str> {
        let r = if simd256_support() {
            unsafe {
                Hacl_Chacha20Poly1305_256_aead_decrypt(
                    key.as_ptr() as _,
                    iv.as_ptr() as _,
                    aad.len() as u32,
                    aad.as_ptr() as _,
                    ctxt_msg.len() as u32,
                    ctxt_msg.as_ptr() as _,
                    ctxt_msg.as_mut_ptr(),
                    tag.as_ptr() as _,
                )
            }
        } else if simd128_support() {
            unsafe {
                Hacl_Chacha20Poly1305_128_aead_decrypt(
                    key.as_ptr() as _,
                    iv.as_ptr() as _,
                    aad.len() as u32,
                    aad.as_ptr() as _,
                    ctxt_msg.len() as u32,
                    ctxt_msg.as_ptr() as _,
                    ctxt_msg.as_mut_ptr(),
                    tag.as_ptr() as _,
                )
            }
        } else {
            unsafe {
                Hacl_Chacha20Poly1305_32_aead_decrypt(
                    key.as_ptr() as _,
                    iv.as_ptr() as _,
                    aad.len() as u32,
                    aad.as_ptr() as _,
                    ctxt_msg.len() as u32,
                    ctxt_msg.as_ptr() as _,
                    ctxt_msg.as_mut_ptr(),
                    tag.as_ptr() as _,
                )
            }
        };
        if r != 0 {
            Err("Decryption error")
        } else {
            Ok(())
        }
    }
}
