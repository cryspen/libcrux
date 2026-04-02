use core::marker::PhantomData;

use super::{DrbgError, GenerateError, HmacAlgorithm, HmacDrbg, ReseedError, MAX_GENERATE_BYTES};

#[cfg(feature = "health-tests")]
use super::health_tests::HealthState;

/// An RNG that is reseedable.
pub trait TryReseedableRng: rand::TryRng
where
    Self::Error: DrbgError,
{
    /// The type of entropy that is required.
    type Entropy: AsRef<[u8]>;

    /// The error that the reseeding operation returns.
    type ReseedError: core::error::Error;

    /// The method that reseeds the RNG with the given entropy and additional input
    fn reseed(
        &mut self,
        entropy_input: &Self::Entropy,
        additional_input: &[u8],
    ) -> Result<(), Self::ReseedError>;
}

// ---------------------------------------------------------------------------
// Seed type
// ---------------------------------------------------------------------------

/// Seed buffer for [`rand::SeedableRng`] on [`HmacDrbg`].
///
/// A newtype over `[u8; N]` with a manual [`Default`] impl, since
/// `[u8; N]: Default` is only available for N ≤ 32 in the current toolchain.
#[derive(Clone)]
pub struct HmacDrbgSeed<const N: usize>(pub [u8; N]);

impl<const N: usize> Default for HmacDrbgSeed<N> {
    fn default() -> Self {
        Self([0u8; N])
    }
}

impl<const N: usize> AsMut<[u8]> for HmacDrbgSeed<N> {
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.0
    }
}

impl<const N: usize> AsRef<[u8]> for HmacDrbgSeed<N> {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl<const OUTLEN: usize, Alg: HmacAlgorithm<OUTLEN>> rand::TryRng for HmacDrbg<OUTLEN, Alg> {
    type Error = GenerateError;

    fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
        let mut buf = [0u8; 4];
        self.generate(&mut buf, None)?;
        Ok(u32::from_le_bytes(buf))
    }

    fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
        let mut buf = [0u8; 8];
        self.generate(&mut buf, None)?;
        Ok(u64::from_le_bytes(buf))
    }

    /// Fill `dst` with pseudorandom bytes.
    ///
    /// Requests larger than [`MAX_GENERATE_BYTES`] are split into chunks so
    /// that arbitrarily-sized buffers can be filled without error.
    //
    // #hax: requires self.reseed_counter + (dst.len() / MAX_GENERATE_BYTES) as u64 + 1 <= RESEED_INTERVAL
    // #hax: ensures result.is_ok() ==> dst is fully written
    fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), Self::Error> {
        let mut written = 0;
        while written < dst.len() {
            let chunk = (dst.len() - written).min(MAX_GENERATE_BYTES);
            self.generate(&mut dst[written..written + chunk], None)?;
            written += chunk;
        }
        Ok(())
    }
}

impl<const OUTLEN: usize, Alg: HmacAlgorithm<OUTLEN>> TryReseedableRng for HmacDrbg<OUTLEN, Alg> {
    type Entropy = HmacDrbgSeed<OUTLEN>;

    type ReseedError = ReseedError;

    fn reseed(
        &mut self,
        entropy: &Self::Entropy,
        additional_input: &[u8],
    ) -> Result<(), Self::ReseedError> {
        self.reseed(entropy.as_ref(), additional_input)
    }
}
impl<const OUTLEN: usize, Alg: HmacAlgorithm<OUTLEN>> rand::TryCryptoRng for HmacDrbg<OUTLEN, Alg> {}

/// [`rand::SeedableRng`] implementation for [`HmacDrbg`].
///
/// The seed type is [`HmacDrbgSeed<OUTLEN>`] — 32 bytes for SHA-256,
/// 48 for SHA-384, 64 for SHA-512.
///
/// # Method summary
///
/// | Method | Entropy source | Nonce | Health tests |
/// |--------|---------------|-------|--------------|
/// | [`from_seed`] | caller-supplied (`OUTLEN` B) | none | bypassed |
/// | [`from_rng`] | `OUTLEN` B from `rng` | `OUTLEN` B from `rng` | applied |
/// | [`try_from_rng`] | `OUTLEN` B from `rng` | `OUTLEN` B from `rng` | applied |
///
/// [`from_seed`]: rand::SeedableRng::from_seed
/// [`from_rng`]: rand::SeedableRng::from_rng
/// [`try_from_rng`]: rand::SeedableRng::try_from_rng
///
/// ## `from_seed` and startup health tests
///
/// [`SeedableRng::from_seed`] intentionally bypasses the AIS 31 startup
/// health tests that [`HmacDrbg::new`] applies to the entropy input.
/// `SeedableRng` is a *deterministic* interface: the caller supplies an exact
/// seed, which may include all-zero test vectors.  The continuous health tests
/// that run during [`HmacDrbg::generate`] are still active.
///
/// ## `from_rng` / `try_from_rng` and startup health tests
///
/// Both overrides draw `OUTLEN` bytes of entropy **and** `OUTLEN` bytes of
/// nonce from the supplied RNG and pass them through [`HmacDrbg::new`], so
/// the AIS 31 startup health tests are applied when the `health-tests` feature
/// is enabled.  Panics if `new()` fails (a catastrophic event indicating a
/// broken entropy source).
#[allow(private_bounds)]
impl<const OUTLEN: usize, Alg: HmacAlgorithm<OUTLEN>> rand::SeedableRng for HmacDrbg<OUTLEN, Alg> {
    type Seed = HmacDrbgSeed<OUTLEN>;

    // #hax: requires true   // seed is always [u8; OUTLEN]; update() cannot fail for inputs of this size
    // #hax: ensures result.reseed_counter == 1
    fn from_seed(seed: Self::Seed) -> Self {
        let mut drbg = Self {
            _alg: PhantomData,
            key: [0x00u8; OUTLEN],
            v: [0x01u8; OUTLEN],
            reseed_counter: 1,
            #[cfg(feature = "health-tests")]
            health: HealthState::new(),
        };
        // seed is [u8; OUTLEN]; update() with a single non-empty slice always succeeds.
        drbg.update(&[&seed.0])
            .expect("HMAC_DRBG_Update with a seed of length OUTLEN cannot fail");
        drbg
    }

    /// Instantiate from an infallible RNG, drawing entropy and a nonce.
    ///
    /// Consumes `2 × OUTLEN` bytes from `rng` (`OUTLEN` entropy + `OUTLEN`
    /// nonce) and instantiates through [`HmacDrbg::new`].  Unlike
    /// [`from_seed`], this path applies the AIS 31 startup health tests when
    /// the `health-tests` feature is enabled.
    ///
    /// Panics if [`HmacDrbg::new`] fails (catastrophic entropy-source
    /// failure; should never occur with a correctly operating RNG).
    ///
    /// [`from_seed`]: rand::SeedableRng::from_seed
    // #hax: requires true   // entropy=[u8;OUTLEN], nonce=[u8;OUTLEN]: 2*OUTLEN <= MAX_SEED_BYTES always holds
    // #hax: ensures result.reseed_counter == 1
    fn from_rng<R: rand::Rng + ?Sized>(rng: &mut R) -> Self {
        let mut entropy = [0u8; OUTLEN];
        let mut nonce = [0u8; OUTLEN];
        rng.fill_bytes(&mut entropy);
        rng.fill_bytes(&mut nonce);
        Self::new(&entropy, &nonce, &[])
            .expect("HMAC_DRBG_Instantiate from RNG failed: entropy source produced invalid output")
    }

    /// Instantiate from a fallible RNG, drawing entropy and a nonce.
    ///
    /// Consumes `2 × OUTLEN` bytes from `rng` (`OUTLEN` entropy + `OUTLEN`
    /// nonce) and instantiates through [`HmacDrbg::new`].  Unlike
    /// [`from_seed`], this path applies the AIS 31 startup health tests when
    /// the `health-tests` feature is enabled.
    ///
    /// Returns `Err(rng_error)` if `rng` fails.
    ///
    /// # Warning — trait limitation
    ///
    /// The [`SeedableRng`] trait fixes the error type of this method to
    /// `R::Error` (the RNG's own error type).  It is therefore **impossible**
    /// to forward [`Error::HealthCheckFailed`] — or any other
    /// [`Error`] variant — through this return type without an
    /// `R::Error: From<Error>` bound, which cannot be added to a trait method
    /// override.
    ///
    /// As a consequence, if `feature = "health-tests"` is enabled and the
    /// entropy source fails the AIS 31 startup test, this method **panics**
    /// rather than returning an error.  If you need non-panicking, fully
    /// error-propagating instantiation, use [`HmacDrbg::new_from_rng`]
    /// directly; it returns `Result<Self, Error>` and propagates all failure
    /// modes.
    ///
    /// [`SeedableRng`]: rand::SeedableRng
    /// [`from_seed`]: rand::SeedableRng::from_seed
    // #hax: requires true   // entropy=[u8;OUTLEN], nonce=[u8;OUTLEN]: 2*OUTLEN <= MAX_SEED_BYTES always holds
    // #hax: ensures result.is_ok() ==> result.unwrap().reseed_counter == 1
    fn try_from_rng<R: rand::TryRng + ?Sized>(rng: &mut R) -> Result<Self, R::Error> {
        let mut entropy = [0u8; OUTLEN];
        let mut nonce = [0u8; OUTLEN];
        rng.try_fill_bytes(&mut entropy)?;
        rng.try_fill_bytes(&mut nonce)?;
        Ok(Self::new(&entropy, &nonce, &[]).expect(
            "HMAC_DRBG_Instantiate from RNG failed: entropy source produced invalid output",
        ))
    }
}
