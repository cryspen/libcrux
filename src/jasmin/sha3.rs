use libjade::jade_hash_sha3_256_amd64_ref;

use crate::{
    digest::{digest_size, Algorithm},
    hw_detection::simd256_support,
};

type Sha256Digest = [u8; digest_size(Algorithm::Sha3_256)];

pub fn sha3_256(input: &[u8]) -> Result<Sha256Digest, &'static str> {
    let mut digest = Sha256Digest::default();
    let r = if simd256_support() {
        log::trace!("Jasmin SHA3 avx2");
        unsafe {
            libjade::jade_hash_sha3_256_amd64_avx2(
                digest.as_mut_ptr(),
                input.as_ptr() as _,
                input.len().try_into().unwrap(),
            )
        }
    } else {
        log::trace!("Jasmin SHA3 ref");
        unsafe {
            jade_hash_sha3_256_amd64_ref(
                digest.as_mut_ptr(),
                input.as_ptr() as _,
                input.len().try_into().unwrap(),
            )
        }
    };
    if r != 0 {
        Err("Error while hashing.")
    } else {
        Ok(digest)
    }
}
