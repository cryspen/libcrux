#![allow(dead_code)]

use crate::{Algorithm, Error, HkdfMode};

macro_rules! impl_hkdf {
    ($struct_name:ident,$name:ident, $string_name:literal, $mode:path, $extract:ident, $expand:ident,$hash_len:literal) => {
        #[doc = "Implementation of HKDF backed by"]
        #[doc = $string_name]
        pub struct $struct_name;

        pub mod $name {
            use super::{checked_u32, $struct_name, Algorithm, Error, HkdfMode};

            impl HkdfMode<$hash_len> for $struct_name {
                const MODE: Algorithm = $mode;

                fn extract(
                    prk: &mut [u8; $hash_len],
                    salt: &[u8],
                    ikm: &[u8],
                ) -> Result<(), Error> {
                    extract(prk, salt, ikm)
                }

                fn expand<const OKM_LEN: usize>(
                    okm: &mut [u8; OKM_LEN],
                    prk: &[u8],
                    info: &[u8],
                ) -> Result<(), Error> {
                    expand(okm, prk, info)
                }

                fn expand_vec(prk: &[u8], info: &[u8], okm_len: usize) -> Result<Vec<u8>, Error> {
                    expand_vec(prk, info, okm_len)
                }
            }

            /// HKDF extract using the `salt` and the input key material `ikm`.
            /// The result is written to `prk`.
            ///
            /// Returns nothing on success.
            /// Returns [`Error::ArgumentsTooLarge`] if one of `ikm` or `salt` is longer than
            /// [`u32::MAX`] bytes.
            pub fn extract(
                prk: &mut [u8; $hash_len],
                salt: &[u8],
                ikm: &[u8],
            ) -> Result<(), Error> {
                Ok(crate::hacl::$extract(
                    prk,
                    salt,
                    checked_u32(salt.len())?,
                    ikm,
                    checked_u32(ikm.len())?,
                ))
            }

            /// HKDF expand using the pre-key material `prk` and `info`.
            /// The output is written to `okm`.
            ///
            /// Returns nothing on success.
            /// Returns [`Error::OkmTooLarge`] if the requested `OKM_LEN` is large.
            /// Returns [`Error::ArgumentsTooLarge`] if one of `prk` or `info` is longer than
            /// [`u32::MAX`] bytes.
            pub fn expand<const OKM_LEN: usize>(
                okm: &mut [u8; OKM_LEN],
                prk: &[u8],
                info: &[u8],
            ) -> Result<(), Error> {
                if OKM_LEN > 255 * $hash_len {
                    // Output size is too large. HACL doesn't catch this.
                    return Err(Error::OkmTooLarge);
                }

                Ok(crate::hacl::$expand(
                    okm,
                    prk,
                    checked_u32(prk.len())?,
                    info,
                    checked_u32(info.len())?,
                    checked_u32(OKM_LEN)?,
                ))
            }

            /// HKDF expand using the pre-key material `prk` and `info`. The output length
            /// is defined by the parameter `okm_len`.
            ///
            /// Returns the key material in a [`Vec<u8>`] of length `okm_len` on success.
            /// Returns [`Error::OkmTooLarge`] if the requested `okm_len` is too large.
            /// Returns [`Error::ArgumentsTooLarge`] if `prk` or `info` is longer than [`u32::MAX`] bytes.
            pub fn expand_vec(prk: &[u8], info: &[u8], okm_len: usize) -> Result<Vec<u8>, Error> {
                if okm_len > 255 * $hash_len {
                    // Output size is too large. HACL doesn't catch this.
                    return Err(Error::OkmTooLarge);
                }

                let mut okm = vec![0u8; okm_len];
                crate::hacl::$expand(
                    &mut okm,
                    prk,
                    checked_u32(prk.len())?,
                    info,
                    checked_u32(info.len())?,
                    checked_u32(okm_len)?,
                );
                Ok(okm)
            }

            /// HKDF using the `salt`, input key material `ikm`, `info`.
            /// The result is written to `okm`.
            /// The output length is defined through the length of `okm`.
            /// Calls `extract` and `expand` with the given input.
            ///
            /// Returns nothing on success.
            /// Returns [`Error::OkmTooLarge`] if the requested `OKM_LEN` is too large.
            /// Returns [`Error::ArgumentsTooLarge`] if one of `ikm`, `salt` or `info` is longer
            /// than [`u32::MAX`] bytes.
            pub fn hkdf<const OKM_LEN: usize>(
                okm: &mut [u8; OKM_LEN],
                salt: &[u8],
                ikm: &[u8],
                info: &[u8],
            ) -> Result<(), Error> {
                let mut prk = [0u8; $hash_len];
                extract(&mut prk, salt, ikm)?;
                expand(okm, &prk, info)
            }

            /// HKDF using the `salt`, input key material `ikm`, `info`.
            /// The output length is defined by the parameter `okm_len`.
            /// Calls `extract` and `expand_vec` with the given input.
            ///
            /// Returns the key material in a [`Vec<u8>`] of length `okm_len` on success.
            /// Returns [`Error::OkmTooLarge`] if the requested `okm_len` is too large.
            /// Returns [`Error::ArgumentsTooLarge`] if `salt`, `ikm` or `info` is longer than [`u32::MAX`] bytes.
            pub fn hkdf_vec(
                salt: &[u8],
                ikm: &[u8],
                info: &[u8],
                okm_len: usize,
            ) -> Result<Vec<u8>, Error> {
                let mut prk = [0u8; $hash_len];
                extract(&mut prk, salt, ikm)?;
                expand_vec(&prk, info, okm_len)
            }
        }
    };
}

impl_hkdf!(
    HkdfSha2_256,
    sha2_256,
    "SHA2-256",
    Algorithm::Sha256,
    extract_sha2_256,
    expand_sha2_256,
    32
);

impl_hkdf!(
    HkdfSha2_384,
    sha2_384,
    "SHA2-384",
    Algorithm::Sha384,
    extract_sha2_384,
    expand_sha2_384,
    48
);

impl_hkdf!(
    HkdfSha2_512,
    sha2_512,
    "SHA2-512",
    Algorithm::Sha512,
    extract_sha2_512,
    expand_sha2_512,
    64
);

fn checked_u32(num: usize) -> Result<u32, Error> {
    num.try_into().map_err(|_| Error::ArgumentsTooLarge)
}
