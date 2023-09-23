use libjade::*;

use crate::digest::Algorithm;
use libcrux_platform::simd256_support;

pub fn hash<const LEN: usize>(alg: Algorithm, payload: &[u8]) -> Result<[u8; LEN], &'static str> {
    let mut digest = [0u8; LEN];
    let r = match alg {
        Algorithm::Sha1 => todo!(),
        Algorithm::Sha224 => todo!(),
        Algorithm::Sha256 => unsafe {
            jade_hash_sha256_amd64_ref(
                digest.as_mut_ptr(),
                payload.as_ptr() as _,
                payload.len().try_into().unwrap(),
            )
        },
        Algorithm::Sha384 => todo!(),
        Algorithm::Sha512 => todo!(),
        Algorithm::Blake2s => todo!(),
        Algorithm::Blake2b => todo!(),
        Algorithm::Sha3_224 => {
            if simd256_support() {
                unsafe {
                    libjade::jade_hash_sha3_224_amd64_avx2(
                        digest.as_mut_ptr(),
                        payload.as_ptr() as _,
                        payload.len().try_into().unwrap(),
                    )
                }
            } else {
                unsafe {
                    jade_hash_sha3_224_amd64_ref(
                        digest.as_mut_ptr(),
                        payload.as_ptr() as _,
                        payload.len().try_into().unwrap(),
                    )
                }
            }
        }
        Algorithm::Sha3_256 => {
            if simd256_support() {
                unsafe {
                    libjade::jade_hash_sha3_256_amd64_avx2(
                        digest.as_mut_ptr(),
                        payload.as_ptr() as _,
                        payload.len().try_into().unwrap(),
                    )
                }
            } else {
                unsafe {
                    jade_hash_sha3_256_amd64_ref(
                        digest.as_mut_ptr(),
                        payload.as_ptr() as _,
                        payload.len().try_into().unwrap(),
                    )
                }
            }
        }
        Algorithm::Sha3_384 => {
            if simd256_support() {
                unsafe {
                    libjade::jade_hash_sha3_384_amd64_avx2(
                        digest.as_mut_ptr(),
                        payload.as_ptr() as _,
                        payload.len().try_into().unwrap(),
                    )
                }
            } else {
                unsafe {
                    jade_hash_sha3_384_amd64_ref(
                        digest.as_mut_ptr(),
                        payload.as_ptr() as _,
                        payload.len().try_into().unwrap(),
                    )
                }
            }
        }
        Algorithm::Sha3_512 => {
            if simd256_support() {
                unsafe {
                    libjade::jade_hash_sha3_512_amd64_avx2(
                        digest.as_mut_ptr(),
                        payload.as_ptr() as _,
                        payload.len().try_into().unwrap(),
                    )
                }
            } else {
                unsafe {
                    jade_hash_sha3_512_amd64_ref(
                        digest.as_mut_ptr(),
                        payload.as_ptr() as _,
                        payload.len().try_into().unwrap(),
                    )
                }
            }
        }
    };
    if r != 0 {
        Err("Error while hashing.")
    } else {
        Ok(digest)
    }
}
