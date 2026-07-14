use p256::elliptic_curve::rand_core;

/// A shim for the `rand` crate to work with the `rand_core@0.6` crate.
pub(crate) struct RandShim<'a, R>(pub &'a mut R);

impl<R: rand::Rng> rand_core::RngCore for RandShim<'_, R> {
    fn next_u32(&mut self) -> u32 {
        self.0.next_u32()
    }

    fn next_u64(&mut self) -> u64 {
        self.0.next_u64()
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.0.fill_bytes(dest)
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
        self.0
            .try_fill_bytes(dest)
            .map_err(|infallible| match infallible {})
    }
}

impl<R: rand::CryptoRng> rand_core::CryptoRng for RandShim<'_, R> {}
