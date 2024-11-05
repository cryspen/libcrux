use libcrux_hacl_rs::ed25519;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    SigningError,
    InvalidSignature,
}

pub fn sign(payload: &[u8], private_key: &[u8; 32]) -> Result<[u8; 64], Error> {
    let mut signature = [0u8; 64];
    ed25519::sign(
        &mut signature,
        private_key,
        payload.len().try_into().map_err(|_| Error::SigningError)?,
        payload,
    );

    Ok(signature)
}

pub fn verify(payload: &[u8], public_key: &[u8; 32], signature: &[u8; 64]) -> Result<(), Error> {
    if ed25519::verify(
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
pub fn secret_to_public(sk: &[u8; 32]) -> [u8; 32] {
    let mut out = [0u8; 32];
    ed25519::secret_to_public(&mut out, sk);
    out
}
