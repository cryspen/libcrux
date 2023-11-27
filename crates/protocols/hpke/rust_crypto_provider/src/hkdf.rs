use alloc::{vec, vec::Vec};

use hkdf::Hkdf;
use hpke_rs_crypto::error::Error;
use sha2::{Sha256, Sha384, Sha512};

macro_rules! implement_hkdfs {
    ($name_extract:ident, $name_expand:ident, $hmac_mode:ident, $name:ident) => {
        pub(crate) fn $name_extract(salt: &[u8], ikm: &[u8]) -> Vec<u8> {
            Hkdf::<$hmac_mode>::extract(Some(salt), ikm)
                .0
                .as_slice()
                .into()
        }
        pub(crate) fn $name_expand(
            prk: &[u8],
            info: &[u8],
            output_size: usize,
        ) -> Result<Vec<u8>, Error> {
            let hkdf =
                Hkdf::<$hmac_mode>::from_prk(prk).map_err(|_| Error::HpkeInvalidOutputLength)?;
            let mut okm = vec![0u8; output_size];
            hkdf.expand(info, &mut okm)
                .map_err(|_| Error::HpkeInvalidOutputLength)?;
            Ok(okm)
        }
    };
}

implement_hkdfs!(sha256_extract, sha256_expand, Sha256, HkdfSha256);
implement_hkdfs!(sha384_extract, sha384_expand, Sha384, HkdfSha384);
implement_hkdfs!(sha512_extract, sha512_expand, Sha512, HkdfSha512);
