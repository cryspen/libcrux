use std::ptr::null_mut;

use libcrux_hacl::*;

use crate::digest::{digest_size, Algorithm};
use libcrux_platform::{simd128_support, simd256_support};

#[cfg(not(simd128))]
unsafe fn Hacl_Blake2s_128_blake2s(
    nn: u32,
    output: *mut u8,
    ll: u32,
    d: *mut u8,
    kk: u32,
    k: *mut u8,
) {
    panic!("No SIMD128 support compiled for HACL.")
}

#[cfg(not(simd256))]
unsafe fn Hacl_Blake2b_256_blake2b(
    nn: u32,
    output: *mut u8,
    ll: u32,
    d: *mut u8,
    kk: u32,
    k: *mut u8,
) {
    panic!("No SIMD256 support compiled for HACL.")
}

pub fn hacl_hash<const LEN: usize>(alg: Algorithm, payload: &[u8]) -> [u8; LEN] {
    let mut digest = [0u8; LEN];
    assert_eq!(LEN, digest_size(alg), "Invalid output digest size");
    match alg {
        Algorithm::Sha1 => todo!(),
        Algorithm::Sha224 => unsafe {
            Hacl_Hash_SHA2_hash_224(
                payload.as_ptr() as _,
                payload.len().try_into().unwrap(),
                digest.as_mut_ptr(),
            );
        },
        Algorithm::Sha256 => unsafe {
            Hacl_Hash_SHA2_hash_256(
                payload.as_ptr() as _,
                payload.len().try_into().unwrap(),
                digest.as_mut_ptr(),
            );
        },
        Algorithm::Sha384 => unsafe {
            Hacl_Hash_SHA2_hash_384(
                payload.as_ptr() as _,
                payload.len().try_into().unwrap(),
                digest.as_mut_ptr(),
            );
        },
        Algorithm::Sha512 => unsafe {
            Hacl_Hash_SHA2_hash_512(
                payload.as_ptr() as _,
                payload.len().try_into().unwrap(),
                digest.as_mut_ptr(),
            );
        },
        Algorithm::Blake2s => {
            assert!(LEN <= 32);
            if simd128_support() {
                unsafe {
                    Hacl_Blake2s_128_blake2s(
                        LEN.try_into().unwrap(),
                        digest.as_mut_ptr(),
                        payload.len().try_into().unwrap(),
                        payload.as_ptr() as _,
                        0,
                        null_mut(),
                    )
                }
            } else {
                unsafe {
                    Hacl_Blake2s_32_blake2s(
                        LEN.try_into().unwrap(),
                        digest.as_mut_ptr(),
                        payload.len().try_into().unwrap(),
                        payload.as_ptr() as _,
                        0,
                        null_mut(),
                    )
                }
            }
        }
        Algorithm::Blake2b => {
            assert!(LEN <= 64);
            if simd256_support() {
                unsafe {
                    Hacl_Blake2b_256_blake2b(
                        LEN.try_into().unwrap(),
                        digest.as_mut_ptr(),
                        payload.len().try_into().unwrap(),
                        payload.as_ptr() as _,
                        0,
                        null_mut(),
                    )
                }
            } else {
                unsafe {
                    Hacl_Blake2b_32_blake2b(
                        LEN.try_into().unwrap(),
                        digest.as_mut_ptr(),
                        payload.len().try_into().unwrap(),
                        payload.as_ptr() as _,
                        0,
                        null_mut(),
                    )
                }
            }
        }
        Algorithm::Sha3_224 => unsafe {
            Hacl_SHA3_sha3_224(
                payload.len().try_into().unwrap(),
                payload.as_ptr() as _,
                digest.as_mut_ptr(),
            );
        },
        Algorithm::Sha3_256 => unsafe {
            Hacl_SHA3_sha3_256(
                payload.len().try_into().unwrap(),
                payload.as_ptr() as _,
                digest.as_mut_ptr(),
            );
        },
        Algorithm::Sha3_384 => unsafe {
            Hacl_SHA3_sha3_384(
                payload.len().try_into().unwrap(),
                payload.as_ptr() as _,
                digest.as_mut_ptr(),
            );
        },
        Algorithm::Sha3_512 => unsafe {
            Hacl_SHA3_sha3_512(
                payload.len().try_into().unwrap(),
                payload.as_ptr() as _,
                digest.as_mut_ptr(),
            );
        },
    }
    digest
}

// SHAKE messages from SHA 3

/// SHAKE 128
pub fn shake128(data: &[u8], out_len: usize) -> Vec<u8> {
    let mut out = vec![0u8; out_len];
    unsafe {
        Hacl_SHA3_shake128_hacl(
            data.len() as u32,
            data.as_ptr() as _,
            out_len as u32,
            out.as_mut_ptr(),
        );
    }
    out
}

/// SHAKE 256
pub fn shake256(data: &[u8], out_len: usize) -> Vec<u8> {
    let mut out = vec![0u8; out_len];
    unsafe {
        Hacl_SHA3_shake256_hacl(
            data.len() as u32,
            data.as_ptr() as _,
            out_len as u32,
            out.as_mut_ptr(),
        );
    }
    out
}

