use libjade_sha256::jade_hash_sha256_amd64_ref;

pub type Sha256Digest = [u8; 32];

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
    use std::fmt::Write;

    fn bytes_to_hex(bytes: &[u8]) -> String {
        let mut s = String::with_capacity(2 * bytes.len());
        for byte in bytes {
            write!(s, "{:02x}", byte).unwrap();
        }
        s
    }

    #[test]
    fn hashit() {
        let input = b"jasmin rulez" as &[u8];
        let digest = sha256(input).unwrap();

        println!("{:x?}", digest);
        let expected = "16096ecad8aa127418804b21c8e2fe93c31453d66a7e9588a429813c968bddd1";
        assert_eq!(expected, bytes_to_hex(&digest));
    }
}
