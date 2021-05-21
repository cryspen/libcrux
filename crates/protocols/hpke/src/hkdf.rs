use evercrypt::prelude::*;

use crate::kdf::*;

macro_rules! implement_hkdfs {
    ($hmac_mode:expr, $name:ident) => {
        #[derive(Debug)]
        pub(crate) struct $name {}
        impl $name {}
        impl KdfTrait for $name {
            fn new() -> Self {
                Self {}
            }
            fn digest_length(&self) -> usize {
                tag_size($hmac_mode)
            }
            fn extract(&self, salt: &[u8], ikm: &[u8]) -> Vec<u8> {
                hkdf_extract($hmac_mode, &salt, &ikm)
            }
            fn expand(&self, prk: &[u8], info: &[u8], output_size: usize) -> Vec<u8> {
                hkdf_expand($hmac_mode, &prk, &info, output_size)
            }
        }
    };
}

implement_hkdfs!(HmacMode::Sha256, HkdfSha256);
implement_hkdfs!(HmacMode::Sha384, HkdfSha384);
implement_hkdfs!(HmacMode::Sha512, HkdfSha512);
