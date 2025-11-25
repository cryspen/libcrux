//! # Ciphersuite Builder
//!
//! This module provides a builder pattern for PSQ ciphersuites.

use libcrux_ed25519::{SigningKey, VerificationKey};
use libcrux_kem::{MlKem768PrivateKey, MlKem768PublicKey};
use libcrux_ml_dsa::ml_dsa_65::{MLDSA65SigningKey, MLDSA65VerificationKey};

#[cfg(feature = "classic-mceliece")]
use crate::classic_mceliece::{PublicKey, SecretKey};
use crate::handshake::{
    builders::BuilderError,
    ciphersuite::{
        initiator::{InitiatorCiphersuite, PqKemPublicKey},
        responder::{PqKemKeyPair, ResponderCiphersuite},
        CiphersuiteName,
    },
    dhkem::{DHKeyPair, DHPublicKey},
};

/// A builder for PSQ handshake ciphersuites.
pub struct CiphersuiteBuilder<'a> {
    name: CiphersuiteName,
    longterm_ecdh_keys: Option<&'a DHKeyPair>,
    longterm_mlkem_encapsulation_key: Option<&'a MlKem768PublicKey>,
    longterm_mlkem_decapsulation_key: Option<&'a MlKem768PrivateKey>,
    longterm_mldsa_signing_key: Option<&'a MLDSA65SigningKey>,
    longterm_mldsa_verification_key: Option<&'a MLDSA65VerificationKey>,
    longterm_ed25519_signing_key: Option<&'a SigningKey>,
    longterm_ed25519_verification_key: Option<&'a VerificationKey>,
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
            longterm_mldsa_signing_key: None,
            longterm_mldsa_verification_key: None,
            longterm_ed25519_signing_key: None,
            longterm_ed25519_verification_key: None,
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

    /// Provide a principal's long-term ML-DSA signing key.
    pub fn longterm_mldsa_signing_key(mut self, signing_key: &'a MLDSA65SigningKey) -> Self {
        self.longterm_mldsa_signing_key = Some(signing_key);
        self
    }

    /// Provide a principal's long-term ML-DSA verification key.
    pub fn longterm_mldsa_verification_key(
        mut self,
        verification_key: &'a MLDSA65VerificationKey,
    ) -> Self {
        self.longterm_mldsa_verification_key = Some(verification_key);
        self
    }

    /// Provide a principal's long-term Ed25519 signing key.
    pub fn longterm_ed25519_signing_key(mut self, signing_key: &'a SigningKey) -> Self {
        self.longterm_ed25519_signing_key = Some(signing_key);
        self
    }

    /// Provide a principal's long-term Ed25519 verification key.
    pub fn longterm_ed25519_verification_key(
        mut self,
        verification_key: &'a VerificationKey,
    ) -> Self {
        self.longterm_ed25519_verification_key = Some(verification_key);
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
    pub fn build_initiator_ciphersuite(self) -> Result<InitiatorCiphersuite<'a>, BuilderError> {
        let Some(kex) = self.peer_longterm_ecdh_pk else {
            return Err(BuilderError::CiphersuiteBuilderState);
        };

        let pq = match self.name {
            CiphersuiteName::X25519_NONE_X25519_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_NONE_X25519_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_NONE_ED25519_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_NONE_ED25519_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_NONE_MLDSA65_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_NONE_MLDSA65_AESGCM128_HKDFSHA256 => PqKemPublicKey::None,

            CiphersuiteName::X25519_MLKEM768_X25519_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_MLKEM768_MLDSA65_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_MLKEM768_X25519_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_MLKEM768_ED25519_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_MLKEM768_ED25519_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_MLKEM768_MLDSA65_CHACHA20POLY1305_HKDFSHA256 => {
                let Some(pq) = self.peer_longterm_mlkem_pk else {
                    return Err(BuilderError::CiphersuiteBuilderState);
                };
                pq.into()
            }

            #[cfg(feature = "classic-mceliece")]
            CiphersuiteName::X25519_CLASSICMCELIECE_ED25519_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_MLDSA65_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_X25519_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_MLDSA65_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_X25519_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_ED25519_CHACHA20POLY1305_HKDFSHA256 => {
                let Some(pq) = self.peer_longterm_cmc_pk else {
                    return Err(BuilderError::CiphersuiteBuilderState);
                };
                pq.into()
            }

            #[cfg(not(feature = "classic-mceliece"))]
            CiphersuiteName::X25519_CLASSICMCELIECE_ED25519_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_MLDSA65_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_X25519_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_MLDSA65_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_X25519_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_ED25519_CHACHA20POLY1305_HKDFSHA256 => {
                return Err(BuilderError::UnsupportedCiphersuite);
            }
        };

        #[cfg(feature = "classic-mceliece")]
        let auth = match self.name {
            CiphersuiteName::X25519_NONE_X25519_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_MLKEM768_X25519_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_NONE_X25519_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_X25519_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_X25519_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_MLKEM768_X25519_AESGCM128_HKDFSHA256 => {
                let Some(auth) = self.longterm_ecdh_keys else {
                    return Err(BuilderError::CiphersuiteBuilderState);
                };
                auth.into()
            }

            CiphersuiteName::X25519_NONE_ED25519_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_MLKEM768_ED25519_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_ED25519_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_NONE_ED25519_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_MLKEM768_ED25519_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_ED25519_AESGCM128_HKDFSHA256 => {
                let Some(auth_sk) = self.longterm_ed25519_signing_key else {
                    return Err(BuilderError::CiphersuiteBuilderState);
                };
                let Some(auth_vk) = self.longterm_ed25519_verification_key else {
                    return Err(BuilderError::CiphersuiteBuilderState);
                };
                (auth_sk, auth_vk).into()
            }

            CiphersuiteName::X25519_NONE_MLDSA65_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_MLKEM768_MLDSA65_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_MLDSA65_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_NONE_MLDSA65_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_MLKEM768_MLDSA65_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_MLDSA65_AESGCM128_HKDFSHA256 => {
                let Some(auth_sk) = self.longterm_mldsa_signing_key else {
                    return Err(BuilderError::CiphersuiteBuilderState);
                };
                let Some(auth_vk) = self.longterm_mldsa_verification_key else {
                    return Err(BuilderError::CiphersuiteBuilderState);
                };
                (auth_sk, auth_vk).into()
            }
        };

        #[cfg(not(feature = "classic-mceliece"))]
        let auth = match self.name {
            CiphersuiteName::X25519_NONE_X25519_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_MLKEM768_X25519_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_NONE_X25519_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_MLKEM768_X25519_AESGCM128_HKDFSHA256 => {
                let Some(auth) = self.longterm_ecdh_keys else {
                    return Err(BuilderError::CiphersuiteBuilderState);
                };
                auth.into()
            }

            CiphersuiteName::X25519_NONE_ED25519_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_MLKEM768_ED25519_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_NONE_ED25519_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_MLKEM768_ED25519_AESGCM128_HKDFSHA256 => {
                let Some(auth_sk) = self.longterm_ed25519_signing_key else {
                    return Err(BuilderError::CiphersuiteBuilderState);
                };
                let Some(auth_vk) = self.longterm_ed25519_verification_key else {
                    return Err(BuilderError::CiphersuiteBuilderState);
                };
                (auth_sk, auth_vk).into()
            }

            CiphersuiteName::X25519_NONE_MLDSA65_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_MLKEM768_MLDSA65_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_NONE_MLDSA65_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_MLKEM768_MLDSA65_AESGCM128_HKDFSHA256 => {
                let Some(auth_sk) = self.longterm_mldsa_signing_key else {
                    return Err(BuilderError::CiphersuiteBuilderState);
                };
                let Some(auth_vk) = self.longterm_mldsa_verification_key else {
                    return Err(BuilderError::CiphersuiteBuilderState);
                };
                (auth_sk, auth_vk).into()
            }

            CiphersuiteName::X25519_CLASSICMCELIECE_X25519_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_X25519_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_ED25519_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_ED25519_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_MLDSA65_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_MLDSA65_AESGCM128_HKDFSHA256 => {
                return Err(BuilderError::UnsupportedCiphersuite)
            }
        };

        Ok(InitiatorCiphersuite {
            name: self.name,
            kex,
            pq,
            auth,
        })
    }

    /// Finish building an [`InitiatorCiphersuite`].
    pub fn build_responder_ciphersuite(self) -> Result<ResponderCiphersuite<'a>, BuilderError> {
        let Some(kex) = self.longterm_ecdh_keys else {
            return Err(BuilderError::CiphersuiteBuilderState);
        };

        let pq = match self.name {
            CiphersuiteName::X25519_NONE_X25519_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_NONE_X25519_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_NONE_ED25519_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_NONE_ED25519_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_NONE_MLDSA65_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_NONE_MLDSA65_AESGCM128_HKDFSHA256 => PqKemKeyPair::None,

            CiphersuiteName::X25519_MLKEM768_X25519_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_MLKEM768_MLDSA65_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_MLKEM768_X25519_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_MLKEM768_ED25519_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_MLKEM768_ED25519_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_MLKEM768_MLDSA65_CHACHA20POLY1305_HKDFSHA256 => {
                let Some(pqpk) = self.longterm_mlkem_encapsulation_key else {
                    return Err(BuilderError::CiphersuiteBuilderState);
                };
                let Some(pqsk) = self.longterm_mlkem_decapsulation_key else {
                    return Err(BuilderError::CiphersuiteBuilderState);
                };
                (pqsk, pqpk).into()
            }

            #[cfg(feature = "classic-mceliece")]
            CiphersuiteName::X25519_CLASSICMCELIECE_ED25519_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_MLDSA65_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_X25519_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_MLDSA65_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_X25519_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_ED25519_CHACHA20POLY1305_HKDFSHA256 => {
                let Some(pqpk) = self.longterm_cmc_encapsulation_key else {
                    return Err(BuilderError::CiphersuiteBuilderState);
                };
                let Some(pqsk) = self.longterm_cmc_decapsulation_key else {
                    return Err(BuilderError::CiphersuiteBuilderState);
                };
                (pqsk, pqpk).into()
            }

            #[cfg(not(feature = "classic-mceliece"))]
            CiphersuiteName::X25519_CLASSICMCELIECE_ED25519_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_MLDSA65_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_X25519_CHACHA20POLY1305_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_MLDSA65_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_X25519_AESGCM128_HKDFSHA256
            | CiphersuiteName::X25519_CLASSICMCELIECE_ED25519_CHACHA20POLY1305_HKDFSHA256 => {
                return Err(BuilderError::UnsupportedCiphersuite);
            }
        };

        Ok(ResponderCiphersuite {
            name: self.name,
            kex,
            pq,
        })
    }
}
