// Allow dead code for now.
// The libjade code here isn't verified yet and thus isn't used.
#![allow(dead_code)]

use libjade_sys::jade_hash_sha256_amd64_ref;

type Sha256Digest = [u8; 32];

pub fn sha256(input: &[u8]) -> Result<Sha256Digest, &'static str> {
    let mut digest = Sha256Digest::default();
    let r = unsafe {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::jasmin::testing::bytes_to_hex;

    #[test]
    fn test_hash() {
        let _ = pretty_env_logger::try_init();

        let input = b"jasmin rulez" as &[u8];
        let digest = sha256(input).unwrap();

        println!("{:x?}", digest);
        let expected = "16096ecad8aa127418804b21c8e2fe93c31453d66a7e9588a429813c968bddd1";
        assert_eq!(expected, bytes_to_hex(&digest));
    }
}
