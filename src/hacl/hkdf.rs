#![allow(dead_code)]

/// HKDF Errors.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The requested output key material in expand was too large for the used
    /// hash function.
    OkmTooLarge,
    /// At least one function argument has been too large to process.
    ArgumentsTooLarge,
}

macro_rules! impl_hkdf {
    ($name:ident,$extract:ident,$expand:ident,$tag_len:literal) => {
        pub mod $name {
            use super::Error;

            /// HKDF extract using the `salt`, and the input key material `ikm`.
            /// Returns the pre-key material in an array of tag length.
            ///
            /// Note that this function panics if `salt` or `ikm` is larger than 2**32 bytes.
            pub fn extract(salt: &[u8], ikm: &[u8]) -> [u8; $tag_len] {
                let mut prk = [0u8; $tag_len];
                unsafe {
                    libcrux_hacl::$extract(
                        prk.as_mut_ptr(),
                        salt.as_ptr() as _,
                        salt.len().try_into().unwrap(),
                        ikm.as_ptr() as _,
                        ikm.len().try_into().unwrap(),
                    );
                }
                prk
            }

            /// HKDF expand using the pre-key material `prk` and `info`. The output length
            /// is defined through the result type.
            /// Returns the key material in an array of length `okm_len` or
            /// [`Error::OkmTooLarge`] if the requested `okm_len` is too large.
            ///
            /// Note that this function returns an [`Error::ArgumentsTooLarge`]
            /// if `salt`, `ikm`, or `OKM_LEN` is larger than 2**32 bytes.
            pub fn expand<const OKM_LEN: usize>(
                prk: &[u8],
                info: &[u8],
            ) -> Result<[u8; OKM_LEN], Error> {
                if OKM_LEN > 255 * $tag_len {
                    // Output size is too large. HACL doesn't catch this.
                    return Err(Error::OkmTooLarge);
                }
                let mut okm = [0u8; OKM_LEN];
                unsafe {
                    libcrux_hacl::$expand(
                        okm.as_mut_ptr(),
                        prk.as_ptr() as _,
                        prk.len().try_into().map_err(|_| Error::ArgumentsTooLarge)?,
                        info.as_ptr() as _,
                        info.len()
                            .try_into()
                            .map_err(|_| Error::ArgumentsTooLarge)?,
                        OKM_LEN.try_into().map_err(|_| Error::ArgumentsTooLarge)?,
                    );
                }
                Ok(okm)
            }

            /// HKDF using the `salt`, input key material `ikm`, `info`. The output length
            /// is defined through the result type.
            /// Calls `extract` and `expand` with the given input.
            ///
            /// Returns the key material in an array of length `okm_len`.
            pub fn hkdf<const OKM_LEN: usize>(
                salt: &[u8],
                ikm: &[u8],
                info: &[u8],
            ) -> Result<[u8; OKM_LEN], Error> {
                let prk = extract(salt, ikm);
                expand(&prk, info)
            }

            /// This module uses heap allocated vectors for cases where the output
            /// length is not const.
            pub mod vec {
                use super::super::Error;

                /// HKDF expand using the pre-key material `prk` and `info`. The output length
                /// is defined through the result type.
                /// Returns the key material in an array of length `okm_len` or
                /// [`Error::OkmTooLarge`] if the requested `okm_len` is too large.
                ///
                /// Note that this function returns an [`Error::ArgumentsTooLarge`]
                /// if `salt`, `ikm`, or `OKM_LEN` is larger than 2**32 bytes.
                pub fn expand(prk: &[u8], info: &[u8], okm_len: usize) -> Result<Vec<u8>, Error> {
                    if okm_len > 255 * $tag_len {
                        // Output size is too large. HACL doesn't catch this.
                        return Err(Error::OkmTooLarge);
                    }
                    let mut okm = vec![0u8; okm_len];
                    unsafe {
                        libcrux_hacl::$expand(
                            okm.as_mut_ptr(),
                            prk.as_ptr() as _,
                            prk.len().try_into().map_err(|_| Error::ArgumentsTooLarge)?,
                            info.as_ptr() as _,
                            info.len()
                                .try_into()
                                .map_err(|_| Error::ArgumentsTooLarge)?,
                            okm_len.try_into().map_err(|_| Error::ArgumentsTooLarge)?,
                        );
                    }
                    Ok(okm)
                }
            }
        }
    };
}

impl_hkdf!(
    sha2_256,
    Hacl_HKDF_extract_sha2_256,
    Hacl_HKDF_expand_sha2_256,
    32
);

impl_hkdf!(
    sha2_384,
    Hacl_HKDF_extract_sha2_384,
    Hacl_HKDF_expand_sha2_384,
    48
);

impl_hkdf!(
    sha2_512,
    Hacl_HKDF_extract_sha2_512,
    Hacl_HKDF_expand_sha2_512,
    64
);
