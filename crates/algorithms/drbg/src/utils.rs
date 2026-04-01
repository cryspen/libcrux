use super::*;

impl<const OUTLEN: usize, Alg: HmacAlgorithm<OUTLEN>> fmt::Debug for HmacDrbg<OUTLEN, Alg> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = f.debug_struct("HmacDrbg");
        s.field("key", &"<redacted>")
            .field("v", &"<redacted>")
            .field("reseed_counter", &self.reseed_counter);

        #[cfg(feature = "health-tests")]
        s.field("poisoned", &self.health.poisoned());

        s.finish()
    }
}

impl fmt::Display for GenerateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            GenerateError::ReseedRequired => f.write_str("reseed required before next generate"),
            GenerateError::RequestTooLarge => f.write_str("generate request size out of range"),
            GenerateError::InputTooLarge => {
                f.write_str("seed material exceeds maximum allowed size")
            }
            #[cfg(feature = "rand")]
            GenerateError::RngError => f.write_str("RNG source failed"),
            #[cfg(feature = "health-tests")]
            GenerateError::HealthCheckFailed => {
                f.write_str("continuous health test failed: DRBG is permanently poisoned")
            }
        }
    }
}

impl<const OUTLEN: usize, Alg: HmacAlgorithm<OUTLEN>> Drop for HmacDrbg<OUTLEN, Alg> {
    #[allow(unsafe_code)]
    fn drop(&mut self) {
        // Overwrite key material with zeros. Using write_volatile prevents the
        // compiler from optimising away the writes as "dead stores".
        for b in self.key.iter_mut() {
            unsafe { core::ptr::write_volatile(b, 0) };
        }
        for b in self.v.iter_mut() {
            unsafe { core::ptr::write_volatile(b, 0) };
        }
        atomic::compiler_fence(atomic::Ordering::SeqCst);
        // HealthState::Drop zeroes its own output-derived bytes automatically.
    }
}

impl From<UpdateError> for InstantiateError {
    fn from(error: UpdateError) -> Self {
        match error {
            UpdateError::InputTooLarge => InstantiateError::InputTooLarge,
        }
    }
}

impl From<UpdateError> for GenerateError {
    fn from(_: UpdateError) -> Self {
        Self::InputTooLarge
    }
}

impl From<super::hmac::Error> for GenerateError {
    fn from(err: super::hmac::Error) -> Self {
        match err {
            super::hmac::Error::InputTooLarge => GenerateError::InputTooLarge,
        }
    }
}
impl From<super::hmac::Error> for UpdateError {
    fn from(err: super::hmac::Error) -> Self {
        match err {
            super::hmac::Error::InputTooLarge => UpdateError::InputTooLarge,
        }
    }
}

impl From<libcrux_hmac::Error> for UpdateError {
    fn from(error: libcrux_hmac::Error) -> Self {
        match error {
            libcrux_hmac::Error::InvalidInputLength => UpdateError::InputTooLarge,
        }
    }
}

pub(super) mod private {
    pub trait Sealed {}
}

impl private::Sealed for HmacSha256 {}
impl private::Sealed for HmacSha384 {}
impl private::Sealed for HmacSha512 {}
