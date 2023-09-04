#![allow(dead_code)]

use libcrux_hacl::{
    Hacl_SHA3_sha3_224, Hacl_SHA3_sha3_256, Hacl_SHA3_sha3_384, Hacl_SHA3_sha3_512,
    Hacl_SHA3_shake128_hacl, Hacl_SHA3_shake256_hacl,
};

/// SHA3 224
pub fn sha224(payload: &[u8]) -> [u8; 28] {
    let mut digest = [0u8; 28];
    unsafe {
        Hacl_SHA3_sha3_224(
            payload.len().try_into().unwrap(),
            payload.as_ptr() as _,
            digest.as_mut_ptr(),
        );
    }
    digest
}

/// SHA3 256
pub fn sha256(payload: &[u8]) -> [u8; 32] {
    let mut digest = [0u8; 32];
    unsafe {
        Hacl_SHA3_sha3_256(
            payload.len().try_into().unwrap(),
            payload.as_ptr() as _,
            digest.as_mut_ptr(),
        );
    }
    digest
}

/// SHA3 384
pub fn sha384(payload: &[u8]) -> [u8; 48] {
    let mut digest = [0u8; 48];
    unsafe {
        Hacl_SHA3_sha3_384(
            payload.len().try_into().unwrap(),
            payload.as_ptr() as _,
            digest.as_mut_ptr(),
        );
    }
    digest
}

/// SHA3 512
pub fn sha512(payload: &[u8]) -> [u8; 64] {
    let mut digest = [0u8; 64];
    unsafe {
        Hacl_SHA3_sha3_512(
            payload.len().try_into().unwrap(),
            payload.as_ptr() as _,
            digest.as_mut_ptr(),
        );
    }
    digest
}

/// SHAKE 128
pub fn shake128<const BYTES: usize>(data: &[u8]) -> [u8; BYTES] {
    let mut out = [0u8; BYTES];
    unsafe {
        Hacl_SHA3_shake128_hacl(
            data.len() as u32,
            data.as_ptr() as _,
            BYTES as u32,
            out.as_mut_ptr(),
        );
    }
    out
}

/// SHAKE 256
///
/// Note that the output length `BYTES` must fit into 32 bit. If it is longer,
/// the output will only return `u32::MAX` bytes.
pub fn shake256<const BYTES: usize>(data: &[u8]) -> [u8; BYTES] {
    let mut out = [0u8; BYTES];
    unsafe {
        Hacl_SHA3_shake256_hacl(
            data.len() as u32,
            data.as_ptr() as _,
            BYTES as u32,
            out.as_mut_ptr(),
        );
    }
    out
}
