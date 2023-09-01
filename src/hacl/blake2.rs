use libcrux_hacl::{Hacl_Blake2b_32_blake2b, Hacl_Blake2s_32_blake2s};

/// BLAKE2b
///
/// Note that the output can not be more than 64. If the requested output is
/// larger than 64, the 64-byte output value is written to the first 64 bytes of
/// the output.
///
/// The payload and key are truncated at 2^32 bytes.
///
/// The `key` may be an empty slice.
#[must_use]
#[inline(always)]
pub fn blake2b<const LEN: usize>(payload: &[u8], key: &[u8]) -> [u8; LEN] {
    let nn = if LEN > 64 { 64u32 } else { LEN as u32 };
    let mut digest = [0u8; LEN];
    unsafe {
        Hacl_Blake2b_32_blake2b(
            nn,
            digest.as_mut_ptr(),
            payload.len() as u32,
            payload.as_ptr() as _,
            key.len() as u32,
            key.as_ptr() as _,
        )
    }
    digest
}

#[cfg(simd256)]
pub mod simd256 {
    use libcrux_hacl::Hacl_Blake2b_256_blake2b;

    /// BLAKE2b
    ///
    /// Note that the output can not be more than 64. If the requested output is
    /// larger than 64, the 64-byte output value is written to the first 64 bytes of
    /// the output.
    ///
    /// The input and key are truncated at 2^32 bytes.
    ///
    /// The `key` may be an empty slice.
    #[must_use]
    #[inline(always)]
    pub fn blake2b<const LEN: usize>(payload: &[u8], key: &[u8]) -> [u8; LEN] {
        let nn = if LEN > 64 { 64u32 } else { LEN as u32 };
        let mut digest = [0u8; LEN];
        unsafe {
            Hacl_Blake2b_256_blake2b(
                nn,
                digest.as_mut_ptr(),
                payload.len() as u32,
                payload.as_ptr() as _,
                key.len() as u32,
                key.as_ptr() as _,
            )
        }
        digest
    }
}

/// BLAKE2s
///
/// Note that the output can not be more than 32. If the requested output is
/// larger than 32, the 32-byte output value is written to the first 32 bytes of
/// the output.
///
/// The input and key are truncated at 2^32 bytes.
///
/// The `key` may be an empty slice.
#[must_use]
#[inline(always)]
pub fn blake2s<const LEN: usize>(payload: &[u8], key: &[u8]) -> [u8; LEN] {
    let nn = if LEN > 32 { 32u32 } else { LEN as u32 };
    let mut digest = [0u8; LEN];
    unsafe {
        Hacl_Blake2s_32_blake2s(
            nn,
            digest.as_mut_ptr(),
            payload.len() as u32,
            payload.as_ptr() as _,
            key.len() as u32,
            key.as_ptr() as _,
        )
    }
    digest
}

#[cfg(simd128)]
pub mod simd128 {
    use libcrux_hacl::Hacl_Blake2s_128_blake2s;

    /// BLAKE2s
    ///
    /// Note that the output can not be more than 32. If the requested output is
    /// larger than 32, the 32-byte output value is written to the first 32 bytes of
    /// the output.
    ///
    /// The input and key are truncated at 2^32 bytes.
    ///
    /// The `key` may be an empty slice.
    #[must_use]
    #[inline(always)]
    pub fn blake2s<const LEN: usize>(payload: &[u8], key: &[u8]) -> [u8; LEN] {
        let nn = if LEN > 64 { 64u32 } else { LEN as u32 };
        let mut digest = [0u8; LEN];
        unsafe {
            Hacl_Blake2s_128_blake2s(
                nn,
                digest.as_mut_ptr(),
                payload.len() as u32,
                payload.as_ptr() as _,
                key.len() as u32,
                key.as_ptr() as _,
            )
        }
        digest
    }
}
