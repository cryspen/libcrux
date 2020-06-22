use digest::Digest;
use hkdf::Hkdf;
use sha2::{Sha256, Sha384, Sha512};

use crate::kdf::*;

macro_rules! implement_hkdfs {
    ($digest:ty, $name:ident, $hash_len:literal) => {
        pub(crate) struct $name {}
        impl $name {}
        impl KdfTrait for $name {
            fn new() -> Self {
                Self {}
            }
            fn digest_length(&self) -> usize {
                <$digest>::output_size()
            }
            fn extract(&self, salt: &[u8], ikm: &[u8]) -> Vec<u8> {
                Hkdf::<$digest>::extract(Some(salt), ikm).0.to_vec()
            }
            fn expand(&self, prk: &[u8], info: &[u8], output_size: usize) -> Vec<u8> {
                let hkdf = match Hkdf::<$digest>::from_prk(prk) {
                    Ok(h) => h,
                    Err(e) => panic!("Invalid PRK for HKDF expand {}", e),
                };
                let mut okm = vec![0u8; output_size];
                match hkdf.expand(info, &mut okm) {
                    Ok(_) => (),
                    Err(e) => panic!("Error in HKDF expand {}", e),
                };
                okm
            }
        }
    };
}

implement_hkdfs!(Sha256, HkdfSha256, 32);
implement_hkdfs!(Sha384, HkdfSha384, 48);
implement_hkdfs!(Sha512, HkdfSha512, 64);
