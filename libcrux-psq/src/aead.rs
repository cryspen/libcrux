//! # AEAD API
use libcrux_chacha20poly1305::{decrypt_detached, encrypt_detached, KEY_LEN, NONCE_LEN};
use libcrux_hkdf::Algorithm;
use tls_codec::{
    Deserialize, Serialize, SerializeBytes, TlsDeserialize, TlsSerialize, TlsSerializeBytes,
    TlsSize,
};

#[derive(Default, Clone, TlsSerialize, TlsDeserialize, TlsSerializeBytes, TlsSize)]
pub struct AEADKey([u8; KEY_LEN], #[tls_codec(skip)] [u8; NONCE_LEN]);

impl std::fmt::Debug for AEADKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("AEADKey").field(&"***").finish()
    }
}

/// Errors arising in the creation or use of AEAD keys
pub enum AEADError {
    CryptoError,
    Serialize(tls_codec::Error),
    Deserialize(tls_codec::Error),
}

impl AEADKey {
    pub(crate) fn new(
        ikm: &impl SerializeBytes,
        info: &impl SerializeBytes,
    ) -> Result<AEADKey, AEADError> {
        let prk = libcrux_hkdf::extract(
            Algorithm::Sha256,
            [],
            ikm.tls_serialize().map_err(AEADError::Serialize)?,
        )
        .map_err(|_| AEADError::CryptoError)?;

        Ok(AEADKey(
            libcrux_hkdf::expand(
                Algorithm::Sha256,
                prk,
                info.tls_serialize().map_err(AEADError::Serialize)?,
                KEY_LEN,
            )
            .map_err(|_| AEADError::CryptoError)?
            .try_into()
            .map_err(|_| AEADError::CryptoError)?, // We don't expect this to fail, unless HDKF gave us the wrong output length,
            [0u8; NONCE_LEN],
        ))
    }

    fn increment_nonce(&mut self) -> Result<(), AEADError> {
        if self.1 == [0xff; NONCE_LEN] {
            return Err(AEADError::CryptoError);
        }
        let mut buf = [0u8; 16];
        buf[16 - NONCE_LEN..].copy_from_slice(self.1.as_slice());
        let mut nonce = u128::from_be_bytes(buf);
        nonce += 1;
        let buf = nonce.to_be_bytes();
        self.1.copy_from_slice(&buf[16 - NONCE_LEN..]);
        Ok(())
    }

    pub(crate) fn encrypt(
        &mut self,
        payload: &[u8],
        aad: &[u8],
        ciphertext: &mut [u8],
    ) -> Result<[u8; 16], AEADError> {
        let mut tag = [0u8; 16];

        self.increment_nonce()?;

        // XXX: We could do better if we'd have an inplace API here.
        let _ = encrypt_detached(&self.0, payload, ciphertext, &mut tag, aad, &self.1)
            .map_err(|_| AEADError::CryptoError)?;

        Ok(tag)
    }

    pub(crate) fn serialize_encrypt<T: Serialize>(
        &mut self,
        payload: &T,
        aad: &[u8],
    ) -> Result<(Vec<u8>, [u8; 16]), AEADError> {
        let serialization_buffer = payload
            .tls_serialize_detached()
            .map_err(AEADError::Serialize)?;

        let mut ciphertext = vec![0u8; serialization_buffer.len()];
        let tag = self.encrypt(&serialization_buffer, aad, &mut ciphertext)?;

        Ok((ciphertext, tag))
    }

    pub(crate) fn decrypt(
        &mut self,
        ciphertext: &[u8],
        tag: &[u8; 16],
        aad: &[u8],
    ) -> Result<Vec<u8>, AEADError> {
        self.increment_nonce()?;
        let mut plaintext = vec![0u8; ciphertext.len()];

        let _ = decrypt_detached(&self.0, &mut plaintext, ciphertext, tag, aad, &self.1)
            .map_err(|_| AEADError::CryptoError)?;

        Ok(plaintext)
    }

    pub(crate) fn decrypt_out(
        &mut self,
        ciphertext: &[u8],
        tag: &[u8; 16],
        aad: &[u8],
        plaintext: &mut [u8],
    ) -> Result<(), AEADError> {
        self.increment_nonce()?;
        debug_assert!(ciphertext.len() <= plaintext.len());

        let _ = decrypt_detached(&self.0, plaintext, ciphertext, tag, aad, &self.1)
            .map_err(|_| AEADError::CryptoError)?;

        Ok(())
    }

    pub(crate) fn decrypt_deserialize<T: Deserialize>(
        &mut self,
        ciphertext: &[u8],
        tag: &[u8; 16],
        aad: &[u8],
    ) -> Result<T, AEADError> {
        let payload_serialized_buf = self.decrypt(ciphertext, tag, aad)?;

        T::tls_deserialize_exact(&payload_serialized_buf).map_err(AEADError::Deserialize)
    }
}
impl AsRef<[u8; KEY_LEN]> for AEADKey {
    fn as_ref(&self) -> &[u8; KEY_LEN] {
        &self.0
    }
}
