use super::{hmac_sha2_256_slices, hmac_sha2_384_slices, hmac_sha2_512_slices, utils, HmacState};

/// The Error returned by the Update operation of HMAC-DRBG.
pub enum Error {
    /// The combined seed material exceeds the internal limit.
    InputTooLarge,
}

// ---------------------------------------------------------------------------
// Algorithm trait
// ---------------------------------------------------------------------------

/// Trait implemented by the three marker types below.
/// Associates a const `OUTLEN` with the HMAC computation for that hash.
pub(super) trait HmacAlgorithm<const OUTLEN: usize>: utils::private::Sealed {
    type State: HmacState<OUTLEN>;

    /// Minimum entropy input length in bytes (SP 800-90A Table 2: security strength).
    ///
    /// For all supported variants this is 32 bytes (256 bits), regardless of `OUTLEN`.
    const SECURITY_STRENGTH: usize;

    /// Single shot HMAC.
    ///
    /// Returns an [`InputTooLarge`] when the input is too long.
    fn hmac(dst: &mut [u8; OUTLEN], key: &[u8], data: &[u8]) -> Result<(), Error>;

    /// New HMAC streaming state.
    ///
    /// Returns the [`Self::State`] or an [`InputTooLarge`] if the `key` is too long.
    fn new_hmac(key: &[u8]) -> Result<Self::State, Error>;
}

/// Marker type selecting HMAC-SHA-256.
#[derive(Debug)]
pub struct HmacSha256;

/// Marker type selecting HMAC-SHA-384.
#[derive(Debug)]
pub struct HmacSha384;

/// Marker type selecting HMAC-SHA-512.
#[derive(Debug)]
pub struct HmacSha512;

impl HmacAlgorithm<32> for HmacSha256 {
    const SECURITY_STRENGTH: usize = 32;
    type State = libcrux_hmac::HmacSha256;

    #[inline]
    fn hmac(dst: &mut [u8; 32], key: &[u8], data: &[u8]) -> Result<(), Error> {
        hmac_sha2_256_slices(dst, key, &[data]).map_err(|_| Error::InputTooLarge)
    }

    #[inline]
    fn new_hmac(key: &[u8]) -> Result<Self::State, Error> {
        libcrux_hmac::HmacSha256::new(key).map_err(|_| Error::InputTooLarge)
    }
}

impl HmacAlgorithm<48> for HmacSha384 {
    const SECURITY_STRENGTH: usize = 48;
    type State = libcrux_hmac::HmacSha384;

    #[inline]
    fn hmac(dst: &mut [u8; 48], key: &[u8], data: &[u8]) -> Result<(), Error> {
        hmac_sha2_384_slices(dst, key, &[data]).map_err(|_| Error::InputTooLarge)
    }

    #[inline]
    fn new_hmac(key: &[u8]) -> Result<Self::State, Error> {
        libcrux_hmac::HmacSha384::new(key).map_err(|_| Error::InputTooLarge)
    }
}

impl HmacAlgorithm<64> for HmacSha512 {
    const SECURITY_STRENGTH: usize = 64;
    type State = libcrux_hmac::HmacSha512;

    #[inline]
    fn hmac(dst: &mut [u8; 64], key: &[u8], data: &[u8]) -> Result<(), Error> {
        hmac_sha2_512_slices(dst, key, &[data]).map_err(|_| Error::InputTooLarge)
    }
    #[inline]
    fn new_hmac(key: &[u8]) -> Result<Self::State, Error> {
        libcrux_hmac::HmacSha512::new(key).map_err(|_| Error::InputTooLarge)
    }
}
