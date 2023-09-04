//! # NIST DRBG
//!
//! Deterministic Random Bit Generator (DRBG) (NIST, SP 800-90A).

use crate::hacl::drbg;
// re-export here for convenience
pub use rand::{CryptoRng, RngCore};

#[derive(Debug)]
pub enum Error {
    /// Invalid input.
    InvalidInput,
    /// The requested digest is not supported.
    UnsupportedAlgorithm,
    /// Unable to generate the requested randomness.
    UnableToGenerate,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{self:?}"))
    }
}

impl std::error::Error for Error {}

pub struct Drbg {
    state: drbg::Drbg,
    ctr: u32, // automatic reseed after 512 invocations. It has to happen at least every 1024 times.
}

impl Drbg {
    /// Create a new DRBG state with the given hash function.
    ///
    /// The DRBG state is initialized with 128 bit entropy from the OS.
    ///
    /// This function requires the `rand` feature.
    #[cfg(feature = "rand")]
    pub fn new(alg: super::digest::Algorithm) -> Result<Self, Error> {
        let mut entropy = [0u8; 16];
        rand::rngs::OsRng.fill_bytes(&mut entropy);
        Self::personalized(alg, &entropy, &[], "os seeded libcrux")
    }

    /// Create a new DRBG state with the given hash function.
    /// This also initializes the DRBG state with the given entropy.
    pub fn new_with_entropy(alg: super::digest::Algorithm, entropy: &[u8]) -> Result<Self, Error> {
        Self::personalized(alg, entropy, &[], "libcrux")
    }

    /// Create a new DRBG state with the given hash function.
    /// This also initializes the DRBG state with the given entropy, nonce and
    /// personalization string.
    pub fn personalized(
        alg: super::digest::Algorithm,
        entropy: &[u8],
        nonce: &[u8],
        personalization: &str,
    ) -> Result<Self, Error> {
        let algorithm = match alg {
            crate::digest::Algorithm::Sha1 => drbg::Algorithm::Sha1,
            crate::digest::Algorithm::Sha256 => drbg::Algorithm::Sha2_256,
            crate::digest::Algorithm::Sha384 => drbg::Algorithm::Sha2_384,
            crate::digest::Algorithm::Sha512 => drbg::Algorithm::Sha2_512,
            crate::digest::Algorithm::Sha224
            | crate::digest::Algorithm::Blake2s
            | crate::digest::Algorithm::Blake2b
            | crate::digest::Algorithm::Sha3_224
            | crate::digest::Algorithm::Sha3_256
            | crate::digest::Algorithm::Sha3_384
            | crate::digest::Algorithm::Sha3_512 => return Err(Error::UnsupportedAlgorithm),
        };

        let state = drbg::Drbg::new(algorithm, entropy, nonce, personalization)
            .map_err(|_| Error::InvalidInput)?;
        Ok(Self { state, ctr: 0 })
    }

    /// Automatically reseed after a while.
    #[cfg(feature = "rand")]
    #[inline(always)]
    fn auto_reseed(&mut self) -> Result<(), Error> {
        if self.ctr > 512 {
            let mut entropy = [0u8; 16];
            rand::rngs::OsRng.fill_bytes(&mut entropy);
            self.reseed(&entropy, b"reseed")?;
            self.ctr = 0;
        } else {
            self.ctr += 1;
        }
        Ok(())
    }

    #[cfg(not(feature = "rand"))]
    #[inline(always)]
    fn auto_reseed(&mut self) -> Result<(), Error> {
        Ok(())
    }

    /// Reseed the DRBG state.
    pub fn reseed(&mut self, entropy: &[u8], additional_input: &[u8]) -> Result<(), Error> {
        self.state
            .reseed(entropy, additional_input)
            .map_err(|_| Error::InvalidInput)
    }

    /// Generate random bytes.
    ///
    /// Note that you will need to call `reseed()` when `reseed_required` is true
    /// and the `rand` feature is not enabled. If the `rand` feature is enabled,
    /// the Drbg reseeds itself when needed, using `OsRng`.
    pub fn generate(&mut self, output: &mut [u8]) -> Result<(), Error> {
        self.auto_reseed()?;
        self.state
            .generate(output, &[])
            .map_err(|_| Error::UnableToGenerate)
    }

    /// Generate random bytes with additional input mixed into the state.
    ///
    /// Note that you will need to call `reseed()` when `reseed_required` is true
    /// and the `rand` feature is not enabled. If the `rand` feature is enabled,
    /// the Drbg reseeds itself when needed, using `OsRng`.
    pub fn generate_with_input(
        &mut self,
        output: &mut [u8],
        additional_input: &[u8],
    ) -> Result<(), Error> {
        self.auto_reseed()?;
        self.state
            .generate(output, additional_input)
            .map_err(|_| Error::UnableToGenerate)
    }

    /// Generate random bytes.
    /// Allocates the vector of length `len`.
    ///
    /// Note that you will need to call `reseed()` when `reseed_required` is true
    /// and the `rand` feature is not enabled. If the `rand` feature is enabled,
    /// the Drbg reseeds itself when needed, using `OsRng`.
    pub fn generate_vec(&mut self, len: usize) -> Result<Vec<u8>, Error> {
        self.auto_reseed()?;
        let mut output = vec![0u8; len];
        self.state
            .generate(&mut output, &[])
            .map_err(|_| Error::UnableToGenerate)
            .map(|()| output)
    }

    /// Generate random bytes.
    /// Allocates the array of length `LEN`.
    ///
    /// Note that you will need to call `reseed()` when `reseed_required` is true
    /// and the `rand` feature is not enabled. If the `rand` feature is enabled,
    /// the Drbg reseeds itself when needed, using `OsRng`.
    pub fn generate_array<const LEN: usize>(&mut self) -> Result<[u8; LEN], Error> {
        self.auto_reseed()?;
        let mut output = [0u8; LEN];
        self.state
            .generate(&mut output, &[])
            .map_err(|_| Error::UnableToGenerate)
            .map(|()| output)
    }

    /// Returns true if a reseed is required and false otherwise.
    pub fn reseed_required(&self) -> bool {
        self.ctr > 512
    }
}

/// Implementation of the [`RngCore`] trait for the [`Drbg`].
impl RngCore for Drbg {
    fn next_u32(&mut self) -> u32 {
        let mut bytes: [u8; 4] = [0; 4];
        self.generate(&mut bytes).unwrap();

        (bytes[0] as u32)
            | (bytes[1] as u32) << 8
            | (bytes[2] as u32) << 16
            | (bytes[3] as u32) << 24
    }

    fn next_u64(&mut self) -> u64 {
        todo!()
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.generate(dest).unwrap()
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand::Error> {
        self.generate(dest).map_err(rand::Error::new)
    }
}

impl CryptoRng for Drbg {}
