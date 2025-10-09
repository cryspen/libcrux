use std::io::Cursor;

use tls_codec::{Deserialize, TlsDeserialize, TlsSerialize, TlsSize};

use crate::handshake::{
    ciphersuite::{
        responder::ResponderCiphersuite, traits::CiphersuiteBase, types::DynamicCiphertext,
    },
    HandshakeError,
};

pub mod builder;
pub mod initiator;
pub mod responder;
pub mod traits;
pub mod types;

#[derive(TlsSize, TlsSerialize, TlsDeserialize, Clone, Copy, Debug, PartialEq)]
#[repr(u8)]
#[allow(non_camel_case_types)]
/// Available ciphersuites for use in the PSQ handshake.
pub enum CiphersuiteName {
    /// Use X25519 for the outer KEM, no inner KEM, Chacha20Poly1305
    /// as payload AEAD and SHA-256 for HKDF. This is the only
    /// ciphersuite supported in Query mode.
    X25519_NONE_CHACHA20POLY1305_HKDFSHA256,
    /// Use X25519 for the outer KEM, ML-KEM 768 for the inner KEM, Chacha20Poly1305 as payload AEAD and SHA-256 for HKDF.
    X25519_MLKEM768_CHACHA20POLY1305_HKDFSHA256,
    /// Use X25519 for the outer KEM, Classic McEliece for the inner KEM, Chacha20Poly1305 as payload AEAD and SHA-256 for HKDF. (requires feature `classic-mceliece`)
    X25519_CLASSICMCELIECE_CHACHA20POLY1305_HKDFSHA256,
    /// Use X25519 for the outer KEM, no inner KEM, AesGcm128 as payload AEAD and SHA-256 for HKDF.
    X25519_NONE_AESGCM128_HKDFSHA256,
    /// Use X25519 for the outer KEM, ML-KEM 768 for the inner KEM, AesGcm128 as payload AEAD and SHA-256 for HKDF.
    X25519_MLKEM768_AESGCM128_HKDFSHA256,
    /// Use X25519 for the outer KEM, Classic McEliece for the inner KEM, AesGcm128 as payload AEAD and SHA-256 for HKDF. (requires feature `classic-mceliece`)
    X25519_CLASSICMCELIECE_AESGCM128_HKDFSHA256,
}

impl CiphersuiteName {
    /// Coerce the responder ciphersuite into a compatible working
    /// ciphersuite for a given handshake.
    ///
    /// A compatible ciphersuite exists, if the PQ KEMs of both ciphersuites
    /// agree, or if the initiator side does not specify a PQ KEM. If the
    /// initiator side specifies a PQ KEM and it does not match the responder
    /// side, there is no compatible ciphersuite.
    ///
    /// If a compatible ciphersuite exists, it will match the initiator
    /// ciphersuite, i.e. a PQ responder ciphersuite can be coerced into a
    /// compatible non-PQ ciphersuite.
    pub(crate) fn coerce_compatible(
        &self,
        responder_ciphersuite: &ResponderCiphersuite,
    ) -> Option<CiphersuiteName> {
        match (self, responder_ciphersuite.name()) {
            (CiphersuiteName::X25519_NONE_CHACHA20POLY1305_HKDFSHA256, _) => {
                Some(CiphersuiteName::X25519_NONE_CHACHA20POLY1305_HKDFSHA256)
            }
            (x, y) if *x == y => Some(y),
            _ => None,
        }
    }

    pub(crate) fn deserialize_encapsulation(
        &self,
        bytes: &[u8],
    ) -> Result<Option<DynamicCiphertext>, HandshakeError> {
        match self {
            CiphersuiteName::X25519_NONE_CHACHA20POLY1305_HKDFSHA256 => Ok(None),
            CiphersuiteName::X25519_MLKEM768_CHACHA20POLY1305_HKDFSHA256 => {
                let enc = Option::<DynamicCiphertext>::tls_deserialize(&mut Cursor::new(bytes))
                    .map_err(|e| HandshakeError::Deserialize(e))?;

                Ok(enc)
            }
            #[cfg(feature = "classic-mceliece")]
            CiphersuiteName::X25519_CLASSICMCELIECE_CHACHA20POLY1305_HKDFSHA256 => {
                use std::io::Cursor;

                let enc = Option::<DynamicCiphertext>::tls_deserialize(&mut Cursor::new(bytes))
                    .map_err(|e| HandshakeError::Deserialize(e))?;
                Ok(enc)
            }
            #[cfg(not(feature = "classic-mceliece"))]
            // This should never happen.
            CiphersuiteName::X25519_CLASSICMCELIECE_CHACHA20POLY1305_HKDFSHA256 => {
                Err(HandshakeError::UnsupportedCiphersuite)
            }
            CiphersuiteName::X25519_NONE_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_MLKEM768_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_AESGCM128_HKDFSHA256 => {
                unimplemented!("AES-GCM 128 ciphersuites are not implemented yet")
            }
        }
    }
}
