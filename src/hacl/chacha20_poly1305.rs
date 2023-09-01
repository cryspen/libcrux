//! # ChaCha20 Poly1305 AEAD
//!
//! This module provides safe Rust APIs for the HACL C functions.
//! The caller MUST ensure that the required hardware features are available
//! before calling the functions.

use libcrux_hacl::{Hacl_Chacha20Poly1305_32_aead_decrypt, Hacl_Chacha20Poly1305_32_aead_encrypt};

pub type Chacha20Key = [u8; 32];
pub type Iv = [u8; 12];
pub type Tag = [u8; 16];

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Error {
    InvalidCiphertext,
}

/// Portable 32-bit in-place encrypt.
///
/// There are no special hardware requirements to call this function.
#[must_use]
pub fn encrypt(key: &Chacha20Key, msg_ctxt: &mut [u8], iv: Iv, aad: &[u8]) -> Tag {
    let mut tag = Tag::default();
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
    tag
}

/// Portable 32-bit in-place decrypt.
///
/// There are no special hardware requirements to call this function.
#[must_use]
pub fn decrypt(
    key: &Chacha20Key,
    ctxt_msg: &mut [u8],
    iv: Iv,
    aad: &[u8],
    tag: &Tag,
) -> Result<(), Error> {
    if unsafe {
        Hacl_Chacha20Poly1305_32_aead_decrypt(
            key.as_ptr() as _,
            iv.as_ptr() as _,
            aad.len() as u32,
            aad.as_ptr() as _,
            ctxt_msg.len() as u32,
            ctxt_msg.as_ptr() as _,
            ctxt_msg.as_mut_ptr(),
            tag.as_ptr() as _,
        ) == 0
    } {
        Ok(())
    } else {
        Err(Error::InvalidCiphertext)
    }
}

#[cfg(simd128)]
pub mod simd128 {
    use super::*;
    use libcrux_hacl::{
        Hacl_Chacha20Poly1305_128_aead_decrypt, Hacl_Chacha20Poly1305_128_aead_encrypt,
    };

    /// 128-bit SIMD encrypt.
    ///
    /// This function requires
    /// * x86_64: AVX, SSE2, SSE3, SSE4.1
    /// * ARM: Arm64, NEON
    /// * s390x: z14
    #[must_use]
    #[inline(always)]
    pub fn encrypt(key: &Chacha20Key, msg_ctxt: &mut [u8], iv: Iv, aad: &[u8]) -> Tag {
        let mut tag = Tag::default();
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
        tag
    }

    /// 128-bit SIMD decrypt.
    ///
    /// This function requires
    /// * x86_64: AVX, SSE2, SSE3, SSE4.1
    /// * ARM: Arm64, NEON
    /// * s390x: z14
    #[must_use]
    #[inline(always)]
    pub fn decrypt(
        key: &Chacha20Key,
        ctxt_msg: &mut [u8],
        iv: Iv,
        aad: &[u8],
        tag: &Tag,
    ) -> Result<(), Error> {
        if unsafe {
            Hacl_Chacha20Poly1305_128_aead_decrypt(
                key.as_ptr() as _,
                iv.as_ptr() as _,
                aad.len() as u32,
                aad.as_ptr() as _,
                ctxt_msg.len() as u32,
                ctxt_msg.as_ptr() as _,
                ctxt_msg.as_mut_ptr(),
                tag.as_ptr() as _,
            ) == 0
        } {
            Ok(())
        } else {
            Err(Error::InvalidCiphertext)
        }
    }
}

#[cfg(simd256)]
pub mod simd256 {
    use super::*;
    use libcrux_hacl::{
        Hacl_Chacha20Poly1305_256_aead_decrypt, Hacl_Chacha20Poly1305_256_aead_encrypt,
    };

    /// 256-bit SIMD encrypt.
    ///
    /// This function requires
    /// * x86_64: AVX, AVX2
    #[must_use]
    #[inline(always)]
    pub fn encrypt(key: &Chacha20Key, msg_ctxt: &mut [u8], iv: Iv, aad: &[u8]) -> Tag {
        let mut tag = Tag::default();
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
        tag
    }

    /// 256-bit SIMD decrypt.
    ///
    /// This function requires
    /// * x86_64: AVX, AVX2
    #[must_use]
    #[inline(always)]
    pub fn decrypt(
        key: &Chacha20Key,
        ctxt_msg: &mut [u8],
        iv: Iv,
        aad: &[u8],
        tag: &Tag,
    ) -> Result<(), Error> {
        if unsafe {
            Hacl_Chacha20Poly1305_256_aead_decrypt(
                key.as_ptr() as _,
                iv.as_ptr() as _,
                aad.len() as u32,
                aad.as_ptr() as _,
                ctxt_msg.len() as u32,
                ctxt_msg.as_ptr() as _,
                ctxt_msg.as_mut_ptr(),
                tag.as_ptr() as _,
            ) == 0
        } {
            Ok(())
        } else {
            Err(Error::InvalidCiphertext)
        }
    }
}
