// Allow dead code for now.
// The libjade code here isn't verified yet and thus isn't used.
#![allow(dead_code)]

use libjade_sys::jade_hash_sha256_amd64_ref;

type Sha256Digest = [u8; 32];

pub fn sha256(input: &[u8]) -> Result<Sha256Digest, &'static str> {
    let mut digest = Sha256Digest::default();
    let r = unsafe {
        log::trace!("Jasmin SHA2 ref");
        jade_hash_sha256_amd64_ref(
            digest.as_mut_ptr(),
            input.as_ptr() as _,
            input.len().try_into().unwrap(),
        )
    };
    if r != 0 {
        Err("Error while hashing.")
    } else {
        Ok(digest)
    }
}
