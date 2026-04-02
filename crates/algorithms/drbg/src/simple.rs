use core::convert::Infallible;

use rand::CryptoRng;

use crate::HmacAlgorithm;

/// A simpler wrapper type that implements rand::CryptoRng, at the loss of some expressivity for
/// Sha256
pub type SimpleHmacSha256Drbg<ReseedRng> = SimpleRng<32, crate::hmac::HmacSha256, ReseedRng>;
/// A simpler wrapper type that implements rand::CryptoRng, at the loss of some expressivity for
/// Sha384
pub type SimpleHmacSha384Drbg<ReseedRng> = SimpleRng<48, crate::hmac::HmacSha384, ReseedRng>;
/// A simpler wrapper type that implements rand::CryptoRng, at the loss of some expressivity for
/// Sha512
pub type SimpleHmacSha512Drbg<ReseedRng> = SimpleRng<64, crate::hmac::HmacSha512, ReseedRng>;

/// A simpler wrapper type that implements rand::CryptoRng, at the loss of some expressivity
#[allow(private_bounds)]
pub struct SimpleRng<const OUTLEN: usize, Hmac: HmacAlgorithm<OUTLEN>, ReseedRng: rand::CryptoRng> {
    drbg: crate::HmacDrbg<OUTLEN, Hmac>,
    rng: ReseedRng,
}

#[allow(private_bounds)]
impl<const OUTLEN: usize, Hmac: HmacAlgorithm<OUTLEN>, ReseedRng: rand::CryptoRng>
    SimpleRng<OUTLEN, Hmac, ReseedRng>
{
    /// Instantiates a new SimpleRng
    pub fn new(mut rng: ReseedRng, nonce: &[u8; 32], personalization: &[u8; 32]) -> Self {
        let mut init_entropy = [0u8; crate::MIN_ENTROPY_BYTES];
        rng.fill_bytes(&mut init_entropy);

        let drbg = match crate::HmacDrbg::new(&init_entropy, nonce, personalization) {
            Ok(drbg) => drbg,
            Err(error) => match error {
                // We ensure the lengths are in bounds by setting fixed lengths in the argument
                // types
                crate::InstantiateError::InputTooLarge => unreachable!(),
            },
        };

        Self { drbg, rng }
    }

    //hax: assume dst.len() < crate::MAX_GENERATE_BYTES
    fn safe_generate_small(&mut self, dst: &mut [u8]) {
        if self.drbg.needs_reseed() {
            match self.drbg.reseed_from_rng(&mut self.rng, &[]) {
                Ok(()) => (),
                // we know how much data we put in and it's fine
                Err(crate::ReseedError::InputTooLarge) => unreachable!(),
            }
        }

        match self.drbg.generate(dst, None) {
            Ok(()) => (),
            // we just ensured that no reseed is required
            Err(crate::GenerateError::ReseedRequired) => unreachable!(),
            // We know how much data we request and it's fine
            Err(crate::GenerateError::RequestTooLarge) => unreachable!(),
            // Again, the input size is safe.
            Err(crate::GenerateError::InputTooLarge) => unreachable!(),
        }
    }
}

impl<const OUTLEN: usize, Hmac: HmacAlgorithm<OUTLEN>, ReseedRng: rand::CryptoRng> rand::TryRng
    for SimpleRng<OUTLEN, Hmac, ReseedRng>
{
    type Error = Infallible;

    fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
        let mut out = [0u8; 4];
        self.safe_generate_small(&mut out);
        Ok(u32::from_le_bytes(out))
    }

    fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
        let mut out = [0u8; 8];
        self.safe_generate_small(&mut out);
        Ok(u64::from_le_bytes(out))
    }

    fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), Self::Error> {
        let (chunks, rest): (&mut [[u8; crate::MAX_GENERATE_BYTES]], _) = dst.as_chunks_mut();

        for chunk in chunks {
            self.safe_generate_small(chunk);
        }

        self.safe_generate_small(rest);

        Ok(())
    }
}

impl<const OUTLEN: usize, Hmac: HmacAlgorithm<OUTLEN>, ReseedRng: rand::CryptoRng>
    rand::TryCryptoRng for SimpleRng<OUTLEN, Hmac, ReseedRng>
{
}

/// Ensure that SimpleRng implements CryptoRng
fn _assert_crypto_rng<
    const OUTLEN: usize,
    Hmac: HmacAlgorithm<OUTLEN>,
    ReseedRng: rand::CryptoRng,
>() {
    fn must_impl<T: CryptoRng>() {}
    must_impl::<SimpleRng<OUTLEN, Hmac, ReseedRng>>();
}
