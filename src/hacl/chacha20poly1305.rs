use libcrux_hacl::*;

use crate::aead::*;
use libcrux_platform::{simd128_support, simd256_support};

#[cfg(simd256)]
fn encrypt_256(key: &Chacha20Key, msg_ctxt: &mut [u8], iv: &Iv, aad: &[u8]) -> Tag {
    log::trace!("HACL Chacha20Poly1305 Encrypt SIMD 256");
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

/// Fallback when simd256 is detected at runtime but it wasn't compiled.
/// We try to fall back to simd128 in this case.
#[cfg(not(simd256))]
fn encrypt_256(key: &Chacha20Key, msg_ctxt: &mut [u8], iv: &Iv, aad: &[u8]) -> Tag {
    encrypt_128(key, msg_ctxt, iv, aad)
}

#[cfg(simd128)]
fn encrypt_128(key: &Chacha20Key, msg_ctxt: &mut [u8], iv: &Iv, aad: &[u8]) -> Tag {
    log::trace!("HACL Chacha20Poly1305 Encrypt SIMD 128");
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

/// Fallback when simd128 is detected at runtime but it wasn't compiled.
/// We try to fall back to portable in this case.
#[cfg(not(simd128))]
fn encrypt_128(key: &Chacha20Key, msg_ctxt: &mut [u8], iv: &Iv, aad: &[u8]) -> Tag {
    encrypt_32(key, msg_ctxt, iv, aad)
}

fn encrypt_32(key: &Chacha20Key, msg_ctxt: &mut [u8], iv: &Iv, aad: &[u8]) -> Tag {
    log::trace!("HACL Chacha20Poly1305 Encrypt Portable");
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

/// Encrypt
/// Returns `tag`
pub(crate) fn encrypt(key: &Chacha20Key, msg_ctxt: &mut [u8], iv: &Iv, aad: &[u8]) -> Tag {
    if simd256_support() {
        encrypt_256(key, msg_ctxt, iv, aad)
    } else if simd128_support() {
        encrypt_128(key, msg_ctxt, iv, aad)
    } else {
        encrypt_32(key, msg_ctxt, iv, aad)
    }
}

#[cfg(simd256)]
fn decrypt_256(key: &Chacha20Key, ctxt_msg: &mut [u8], iv: &Iv, aad: &[u8], tag: &Tag) -> u32 {
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
}

/// Fallback when simd256 is detected at runtime but it wasn't compiled.
/// We try to fall back to simd128 in this case.
#[cfg(not(simd256))]
fn decrypt_256(key: &Chacha20Key, ctxt_msg: &mut [u8], iv: &Iv, aad: &[u8], tag: &Tag) -> u32 {
    decrypt_128(key, ctxt_msg, iv, aad, tag)
}

#[cfg(simd128)]
fn decrypt_128(key: &Chacha20Key, ctxt_msg: &mut [u8], iv: &Iv, aad: &[u8], tag: &Tag) -> u32 {
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
}

/// Fallback when simd128 is detected at runtime but it wasn't compiled.
/// We try to fall back to portable in this case.
#[cfg(not(simd128))]
fn decrypt_128(key: &Chacha20Key, ctxt_msg: &mut [u8], iv: &Iv, aad: &[u8], tag: &Tag) -> u32 {
    decrypt_32(key, ctxt_msg, iv, aad, tag)
}

fn decrypt_32(key: &Chacha20Key, ctxt_msg: &mut [u8], iv: &Iv, aad: &[u8], tag: &Tag) -> u32 {
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
        decrypt_256(key, ctxt_msg, iv, aad, tag)
    } else if simd128_support() {
        decrypt_128(key, ctxt_msg, iv, aad, tag)
    } else {
        decrypt_32(key, ctxt_msg, iv, aad, tag)
    };
    if r != 0 {
        Err("Decryption error")
    } else {
        Ok(())
    }
}
