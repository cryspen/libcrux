use hkdf::Hkdf;
use sha2::{Digest, Sha256, Sha384, Sha512};

use crate::kdf::*;

macro_rules! implement_hkdfs {
    ($hmac_mode:ident, $name:ident) => {
        #[derive(Debug)]
        pub(crate) struct $name {}
        impl $name {}
        impl KdfTrait for $name {
            fn new() -> Self {
                Self {}
            }
            fn digest_length(&self) -> usize {
                $hmac_mode::output_size()
            }
            fn extract(&self, salt: &[u8], ikm: &[u8]) -> Vec<u8> {
                Hkdf::<$hmac_mode>::extract(Some(salt), ikm)
                    .0
                    .as_slice()
                    .into()
            }
            fn expand(
                &self,
                prk: &[u8],
                info: &[u8],
                output_size: usize,
            ) -> Result<Vec<u8>, Error> {
                let hkdf =
                    Hkdf::<$hmac_mode>::from_prk(prk).map_err(|_| Error::InvalidOutputLength)?;
                let mut okm = vec![0u8; output_size];
                hkdf.expand(info, &mut okm)
                    .map_err(|_| Error::InvalidOutputLength)?;
                Ok(okm)
            }
        }
    };
}

implement_hkdfs!(Sha256, HkdfSha256);
implement_hkdfs!(Sha384, HkdfSha384);
implement_hkdfs!(Sha512, HkdfSha512);
