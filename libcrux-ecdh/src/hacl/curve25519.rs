#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Error {
    InvalidInput,
}

/// Compute the ECDH with the `private_key` and `public_key`.
///
/// Returns the 32 bytes shared key.
#[inline(always)]
pub fn ecdh(
    private_key: impl AsRef<[u8; 32]>,
    public_key: impl AsRef<[u8; 32]>,
) -> Result<[u8; 32], Error> {
    let mut shared = [0u8; 32];
    libcrux_curve25519::ecdh(&mut shared, public_key.as_ref(), private_key.as_ref())
        .map(|_| shared)
        .map_err(|_| Error::InvalidInput)
}

/// Compute the public key for the provided `private_key` (scalar multiplication
/// with the base point).
///
/// Returns the 32 bytes shared key.
#[must_use]
#[inline(always)]
pub fn secret_to_public(private_key: impl AsRef<[u8; 32]>) -> [u8; 32] {
    let mut public = [0u8; 32];
    libcrux_curve25519::secret_to_public(&mut public, private_key.as_ref());
    public
}

#[cfg(all(bmi2, adx, target_arch = "x86_64"))]
pub mod vale {
    use super::Error;
    use libcrux_hacl::Hacl_Curve25519_64_ecdh;

    /// Compute the ECDH with the `private_key` and `public_key`.
    ///
    /// Returns the 32 bytes shared key.
    #[inline(always)]
    pub fn ecdh(
        private_key: impl AsRef<[u8; 32]>,
        public_key: impl AsRef<[u8; 32]>,
    ) -> Result<[u8; 32], Error> {
        let mut shared = [0u8; 32];
        let ok = unsafe {
            Hacl_Curve25519_64_ecdh(
                shared.as_mut_ptr(),
                private_key.as_ref().as_ptr() as _,
                public_key.as_ref().as_ptr() as _,
            )
        };
        if !ok {
            Err(Error::InvalidInput)
        } else {
            Ok(shared)
        }
    }
}
