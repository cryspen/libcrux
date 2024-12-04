#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    SigningError,
    InvalidSignature,
}

/// The hacl implementation requires that
/// - the private key is a 32 byte buffer
/// - the signature is a 64 byte buffer,
/// - the payload buffer is not shorter than payload_len.
///
/// We enforce the first two using types, and the latter by using `payload.len()` and `payload_len`.
/// This has the caveat that `payload_len` must be <= u32::MAX, so we return an error if that is
/// not the case.
pub fn sign(payload: &[u8], private_key: &[u8; 32]) -> Result<[u8; 64], Error> {
    let mut signature = [0u8; 64];
    crate::hacl::ed25519::sign(
        &mut signature,
        private_key,
        payload.len().try_into().map_err(|_| Error::SigningError)?,
        payload,
    );

    Ok(signature)
}

/// The hacl implementation requires that
/// - the public key is a 32 byte buffer
/// - the signature is a 64 byte buffer,
/// - the payload buffer is not shorter than payload_len.
///
/// We enforce the first two using types, and the latter by using `payload.len()` and `payload_len`.
/// This has the caveat that `payload_len` must be <= u32::MAX, so we return an error if that is
/// not the case.
///
pub fn verify(payload: &[u8], public_key: &[u8; 32], signature: &[u8; 64]) -> Result<(), Error> {
    if crate::hacl::ed25519::verify(
        public_key,
        payload.len().try_into().map_err(|_| Error::SigningError)?,
        payload,
        signature,
    ) {
        Ok(())
    } else {
        Err(Error::InvalidSignature)
    }
}

/// Compute the public point for the given secret key `sk`.
/// The hacl implementation requires that these are both 32 byte buffers, which we enforce through
/// types.
pub fn secret_to_public(pk: &mut [u8; 32], sk: &[u8; 32]) {
    crate::hacl::ed25519::secret_to_public(pk, sk)
}
