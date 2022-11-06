use libcrux_hacl::{
    Hacl_Hash_SHA2_hash_224, Hacl_Hash_SHA2_hash_256, Hacl_Hash_SHA2_hash_384,
    Hacl_Hash_SHA2_hash_512, Hacl_SHA3_sha3_224, Hacl_SHA3_sha3_256, Hacl_SHA3_sha3_384,
    Hacl_SHA3_sha3_512,
};

use crate::digest::{digest_size, Algorithm};

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
        Algorithm::Blake2s => todo!(),
        Algorithm::Blake2b => todo!(),
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
