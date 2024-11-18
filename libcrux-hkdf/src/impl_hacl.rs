#![allow(dead_code)]

use crate::{Algorithm, Error, HkdfMode};

macro_rules! impl_hkdf {
    ($sname:ident,$name:ident, $mode:path, $extract:ident, $expand:ident,$hash_len:literal) => {
        pub struct $sname;

        pub mod $name {
            use super::{checked_u32, $sname, Algorithm, Error, HkdfMode};

            impl HkdfMode<$hash_len> for $sname {
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
                    vec::expand(prk, info, okm_len)
                }
            }

            /// HKDF extract using the `salt`, and the input key material `ikm`.
            /// Returns the pre-key material in an array of hash length.
            ///
            /// Note that this function returns an [`Error::ArgumentsTooLarge`]
            /// if `salt` or `ikm` is larger than 2**32 bytes.
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

            /// HKDF expand using the pre-key material `prk` and `info`. The output length
            /// is defined through the result type.
            /// Returns the key material in an array of length `okm_len` or
            /// [`Error::OkmTooLarge`] if the requested `okm_len` is too large.
            ///
            /// Note that this function returns an [`Error::ArgumentsTooLarge`]
            /// if `prk`, `info`, or `OKM_LEN` is larger than 2**32 bytes.
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

            /// HKDF using the `salt`, input key material `ikm`, `info`. The output length
            /// is defined through the result type.
            /// Calls `extract` and `expand` with the given input.
            ///
            /// Returns the key material in an array of length `okm_len`.
            /// Note that this function panics if `salt` or `ikm` is longer than  (2**32 - 1) bytes.
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

            /// This module uses heap allocated vectors for cases where the output
            /// length is not const.
            pub mod vec {
                use super::{checked_u32, Error};

                /// HKDF expand using the pre-key material `prk` and `info`. The output length
                /// is defined by the parameter `okm_len`.
                /// Returns the key material in an array of length `okm_len` or
                /// [`Error::OkmTooLarge`] if the requested `okm_len` is too large.
                ///
                /// Note that this function returns an [`Error::ArgumentsTooLarge`]
                /// if `salt`, `ikm`, or `OKM_LEN` is longer than (2**32 - 1) bytes.
                pub fn expand(prk: &[u8], info: &[u8], okm_len: usize) -> Result<Vec<u8>, Error> {
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
            }
        }
    };
}

impl_hkdf!(
    HkdfSha2_256,
    sha2_256,
    Algorithm::Sha256,
    extract_sha2_256,
    expand_sha2_256,
    32
);

impl_hkdf!(
    HkdfSha2_384,
    sha2_384,
    Algorithm::Sha384,
    extract_sha2_384,
    expand_sha2_384,
    48
);

impl_hkdf!(
    HkdfSha2_512,
    sha2_512,
    Algorithm::Sha512,
    extract_sha2_512,
    expand_sha2_512,
    64
);

fn checked_u32(num: usize) -> Result<u32, Error> {
    num.try_into().map_err(|_| Error::ArgumentsTooLarge)
}
