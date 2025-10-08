//! # Ciphersuite Builder
//!
//! This module provides a builder pattern for PSQ ciphersuites.

use libcrux_kem::{MlKem768PrivateKey, MlKem768PublicKey};

#[cfg(feature = "classic-mceliece")]
use crate::classic_mceliece::{PublicKey, SecretKey};
use crate::handshake::{
    ciphersuite::{
        initiator::{
            InitiatorCiphersuite, InitiatorX25519ChachaPolyHkdfSha256,
            InitiatorX25519Mlkem768ChachaPolyHkdfSha256,
        },
        responder::{
            ResponderCiphersuite, ResponderX25519ChaChaPolyHkdfSha256,
            ResponderX25519MlKem768ChaChaPolyHkdfSha256,
        },
        CiphersuiteName,
    },
    dhkem::{DHKeyPair, DHPublicKey},
    HandshakeError,
};

/// A builder for PSQ handshake ciphersuites.
pub struct CiphersuiteBuilder<'a> {
    name: CiphersuiteName,
    longterm_ecdh_keys: Option<&'a DHKeyPair>,
    longterm_mlkem_encapsulation_key: Option<&'a MlKem768PublicKey>,
    longterm_mlkem_decapsulation_key: Option<&'a MlKem768PrivateKey>,
    peer_longterm_ecdh_pk: Option<&'a DHPublicKey>,
    peer_longterm_mlkem_pk: Option<&'a MlKem768PublicKey>,
    #[cfg(feature = "classic-mceliece")]
    longterm_cmc_encapsulation_key: Option<&'a PublicKey>,
    #[cfg(feature = "classic-mceliece")]
    longterm_cmc_decapsulation_key: Option<&'a SecretKey>,
    #[cfg(feature = "classic-mceliece")]
    peer_longterm_cmc_pk: Option<&'a PublicKey>,
}

impl<'a> CiphersuiteBuilder<'a> {
    /// Start building a new ciphersuite.
    pub fn new(name: CiphersuiteName) -> Self {
        Self {
            name,
            longterm_ecdh_keys: None,
            longterm_mlkem_encapsulation_key: None,
            longterm_mlkem_decapsulation_key: None,
            peer_longterm_ecdh_pk: None,
            peer_longterm_mlkem_pk: None,
            #[cfg(feature = "classic-mceliece")]
            longterm_cmc_encapsulation_key: None,
            #[cfg(feature = "classic-mceliece")]
            longterm_cmc_decapsulation_key: None,
            #[cfg(feature = "classic-mceliece")]
            peer_longterm_cmc_pk: None,
        }
    }

    /// Provide a principal's long-term ECDH key pair.
    pub fn longterm_ecdh_keys(mut self, keypair: &'a DHKeyPair) -> Self {
        self.longterm_ecdh_keys = Some(keypair);
        self
    }

    /// Provide a principal's long-term ML-KEM encapsulation key.
    pub fn longterm_mlkem_encapsulation_key(
        mut self,
        encapsulation_key: &'a MlKem768PublicKey,
    ) -> Self {
        self.longterm_mlkem_encapsulation_key = Some(encapsulation_key);
        self
    }

    /// Provide a principal's long-term ML-KEM decapsulation key.
    pub fn longterm_mlkem_decapsulation_key(
        mut self,
        decapsulation_key: &'a MlKem768PrivateKey,
    ) -> Self {
        self.longterm_mlkem_decapsulation_key = Some(decapsulation_key);
        self
    }

    /// Provide a peer's long-term ECDH public key.
    pub fn peer_longterm_ecdh_pk(mut self, ecdh_pk: &'a DHPublicKey) -> Self {
        self.peer_longterm_ecdh_pk = Some(ecdh_pk);
        self
    }

    /// Provide a peer's long-term ML-KEM encapsulation key.
    pub fn peer_longterm_mlkem_pk(mut self, encapsulation_key: &'a MlKem768PublicKey) -> Self {
        self.peer_longterm_mlkem_pk = Some(encapsulation_key);
        self
    }

    #[cfg(feature = "classic-mceliece")]
    /// Provide a principal's long-term Classic McEliece encapsulation key.
    pub fn longterm_cmc_encapsulation_key(mut self, encapsulation_key: &'a PublicKey) -> Self {
        self.longterm_cmc_encapsulation_key = Some(encapsulation_key);
        self
    }

    #[cfg(feature = "classic-mceliece")]
    /// Provide a principal's long-term Classic McEliece decapsulation key.
    pub fn longterm_cmc_decapsulation_key(mut self, decapsulation_key: &'a SecretKey) -> Self {
        self.longterm_cmc_decapsulation_key = Some(decapsulation_key);
        self
    }

    #[cfg(feature = "classic-mceliece")]
    /// Provide a peers's long-term Classic McEliece encapsulation key.
    pub fn peer_longterm_cmc_pk(mut self, encapsulation_key: &'a PublicKey) -> Self {
        self.peer_longterm_cmc_pk = Some(encapsulation_key);
        self
    }

    /// Finish building an [`InitiatorCiphersuite`].
    pub fn build_initiator_ciphersuite(self) -> Result<InitiatorCiphersuite<'a>, HandshakeError> {
        let (peer_longterm_ecdh_pk, longterm_ecdh_keys) = self.check_common_keys_initiator()?;
        match self.name {
            CiphersuiteName::X25519ChachaPolyHkdfSha256 => {
                Ok(InitiatorCiphersuite::X25519_ChaChaPoly_HkdfSha256(
                    InitiatorX25519ChachaPolyHkdfSha256 {
                        longterm_ecdh_keys,
                        peer_longterm_ecdh_pk,
                    },
                ))
            }
            CiphersuiteName::X25519Mlkem768ChachaPolyHkdfSha256 => {
                let Some(peer_longterm_mlkem_pk) = self.peer_longterm_mlkem_pk else {
                    return Err(HandshakeError::CiphersuiteBuilderState);
                };
                Ok(InitiatorCiphersuite::X25519_MlKem768_ChaChaPoly_HkdfSha256(
                    InitiatorX25519Mlkem768ChachaPolyHkdfSha256 {
                        longterm_ecdh_keys,
                        peer_longterm_ecdh_pk,
                        peer_longterm_mlkem_pk,
                    },
                ))
            }
            #[cfg(feature = "classic-mceliece")]
            CiphersuiteName::X25519ClassicMcElieceChachaPolyHkdfSha256 => {
                use crate::handshake::ciphersuite::initiator::InitiatorX25519ClassicMcElieceChachaPolyHkdfSha256;

                let Some(peer_longterm_cmc_pk) = self.peer_longterm_cmc_pk else {
                    return Err(HandshakeError::CiphersuiteBuilderState);
                };
                Ok(
                    InitiatorCiphersuite::X25519_ClassicMcEliece_ChaChaPoly_HkdfSha256(
                        InitiatorX25519ClassicMcElieceChachaPolyHkdfSha256 {
                            longterm_ecdh_keys,
                            peer_longterm_ecdh_pk,
                            peer_longterm_cmc_pk,
                        },
                    ),
                )
            }

            #[cfg(not(feature = "classic-mceliece"))]
            CiphersuiteName::X25519ClassicMcElieceChachaPolyHkdfSha256 => {
                eprintln!("Error building InitiatorCiphersuite: Classic McEliece ciphersuites are only available when using the `classic-mceliece` feature.");
                return Err(HandshakeError::UnsupportedCiphersuite);
            }
        }
    }

    /// Finish building an [`InitiatorCiphersuite`].
    pub fn build_responder_ciphersuite(self) -> Result<ResponderCiphersuite<'a>, HandshakeError> {
        let Some(longterm_ecdh_keys) = self.longterm_ecdh_keys else {
            return Err(HandshakeError::CiphersuiteBuilderState);
        };

        match self.name {
            CiphersuiteName::X25519ChachaPolyHkdfSha256 => {
                Ok(ResponderCiphersuite::X25519_ChaChaPoly_HkdfSha256(
                    ResponderX25519ChaChaPolyHkdfSha256 { longterm_ecdh_keys },
                ))
            }
            CiphersuiteName::X25519Mlkem768ChachaPolyHkdfSha256 => {
                let Some(longterm_pq_encapsulation_key) = self.longterm_mlkem_encapsulation_key
                else {
                    return Err(HandshakeError::CiphersuiteBuilderState);
                };
                let Some(longterm_pq_decapsulation_key) = self.longterm_mlkem_decapsulation_key
                else {
                    return Err(HandshakeError::CiphersuiteBuilderState);
                };

                Ok(ResponderCiphersuite::X25519_MlKem768_ChaChaPoly_HkdfSha256(
                    ResponderX25519MlKem768ChaChaPolyHkdfSha256 {
                        longterm_ecdh_keys,
                        longterm_pq_encapsulation_key,
                        longterm_pq_decapsulation_key,
                    },
                ))
            }
            #[cfg(feature = "classic-mceliece")]
            CiphersuiteName::X25519ClassicMcElieceChachaPolyHkdfSha256 => {
                use crate::handshake::ciphersuite::responder::ResponderX25519ClassicMcElieceChaChaPolyHkdfSha256;

                let Some(longterm_pq_encapsulation_key) = self.longterm_cmc_encapsulation_key
                else {
                    return Err(HandshakeError::CiphersuiteBuilderState);
                };
                let Some(longterm_pq_decapsulation_key) = self.longterm_cmc_decapsulation_key
                else {
                    return Err(HandshakeError::CiphersuiteBuilderState);
                };

                Ok(
                    ResponderCiphersuite::X25519_ClassicMcEliece_ChaChaPoly_HkdfSha256(
                        ResponderX25519ClassicMcElieceChaChaPolyHkdfSha256 {
                            longterm_ecdh_keys,
                            longterm_pq_encapsulation_key,
                            longterm_pq_decapsulation_key,
                        },
                    ),
                )
            }
            #[cfg(not(feature = "classic-mceliece"))]
            CiphersuiteName::X25519ClassicMcElieceChachaPolyHkdfSha256 => {
                eprintln!("Error building InitiatorCiphersuite: Classic McEliece ciphersuites are only available when using the `classic-mceliece` feature.");
                return Err(HandshakeError::UnsupportedCiphersuite);
            }
        }
    }

    fn check_common_keys_initiator(
        &self,
    ) -> Result<(&'a DHPublicKey, &'a DHKeyPair), HandshakeError> {
        let Some(peer_longterm_ecdh_pk) = self.peer_longterm_ecdh_pk else {
            return Err(HandshakeError::CiphersuiteBuilderState);
        };
        let Some(longterm_ecdh_keys) = self.longterm_ecdh_keys else {
            return Err(HandshakeError::CiphersuiteBuilderState);
        };
        Ok((peer_longterm_ecdh_pk, longterm_ecdh_keys))
    }
}
