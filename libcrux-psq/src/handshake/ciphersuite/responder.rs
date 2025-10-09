use libcrux_kem::{MlKem768PrivateKey, MlKem768PublicKey};

#[cfg(feature = "classic-mceliece")]
use crate::classic_mceliece::{PublicKey, SecretKey};
use crate::handshake::{
    ciphersuite::{
        traits::CiphersuiteBase,
        types::{DynamicCiphertext, DynamicEncapsulationKeyRef, DynamicSharedSecret},
        CiphersuiteName,
    },
    dhkem::{DHKeyPair, DHPrivateKey, DHPublicKey},
    HandshakeError,
};

pub struct ResponderX25519ChaCha20Poly1305HkdfSha256<'a> {
    pub longterm_ecdh_keys: &'a DHKeyPair,
}
pub struct ResponderX25519MlKem768ChaCha20Poly1305HkdfSha256<'a> {
    pub longterm_ecdh_keys: &'a DHKeyPair,
    pub longterm_pq_encapsulation_key: &'a MlKem768PublicKey,
    pub longterm_pq_decapsulation_key: &'a MlKem768PrivateKey,
}

#[cfg(feature = "classic-mceliece")]
pub struct ResponderX25519ClassicMcElieceChaCha20Poly1305HkdfSha256<'a> {
    pub longterm_ecdh_keys: &'a DHKeyPair,
    pub longterm_pq_encapsulation_key: &'a PublicKey,
    pub longterm_pq_decapsulation_key: &'a SecretKey,
}

#[allow(non_camel_case_types)]
/// The ciphersuites available to a PSQ responder.
pub enum ResponderCiphersuite<'a> {
    X25519NoneChaCha20Poly1305HkdfSha256(ResponderX25519ChaCha20Poly1305HkdfSha256<'a>),
    X25519MlKem768ChaCha20Poly1305HkdfSha256(ResponderX25519MlKem768ChaCha20Poly1305HkdfSha256<'a>),
    #[cfg(feature = "classic-mceliece")]
    X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(
        ResponderX25519ClassicMcElieceChaCha20Poly1305HkdfSha256<'a>,
    ),
    #[cfg(not(feature = "classic-mceliece"))]
    X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(std::marker::PhantomData<&'a [u8]>),
}

impl<'a> CiphersuiteBase for ResponderCiphersuite<'a> {
    type Ciphertext = DynamicCiphertext;
    type EncapsulationKeyRef = DynamicEncapsulationKeyRef<'a>;
    type SharedSecret = DynamicSharedSecret<'a>;

    fn name(&self) -> CiphersuiteName {
        match self {
            ResponderCiphersuite::X25519MlKem768ChaCha20Poly1305HkdfSha256(_) => {
                CiphersuiteName::X25519_MLKEM768_CHACHAPOLY1305_HKDFSHA256
            }
            #[cfg(feature = "classic-mceliece")]
            ResponderCiphersuite::X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(_) => {
                CiphersuiteName::X25519_CLASSICMCELIECE_CHACHAPOLY1305_HKDFSHA256
            }
            #[cfg(not(feature = "classic-mceliece"))]
            ResponderCiphersuite::X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(_) => {
                // We can never reach this because the ciphersuite can only be constructed with the feature turned on.
                unreachable!("unsupported ciphersuite")
            }
            ResponderCiphersuite::X25519NoneChaCha20Poly1305HkdfSha256(_) => {
                CiphersuiteName::X25519_NONE_CHACHAPOLY1305_HKDFSHA256
            }
        }
    }

    fn own_ecdh_decapsulation_key(&self) -> &DHPrivateKey {
        match self {
            ResponderCiphersuite::X25519MlKem768ChaCha20Poly1305HkdfSha256(
                responder_x25519_mlkem768_chacha_poly_hkdf_sha256,
            ) => {
                &responder_x25519_mlkem768_chacha_poly_hkdf_sha256
                    .longterm_ecdh_keys
                    .sk
            }
            #[cfg(feature = "classic-mceliece")]
            ResponderCiphersuite::X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(
                responder_x25519_classic_mc_eliece_chacha_poly_hkdf_sha256,
            ) => {
                &responder_x25519_classic_mc_eliece_chacha_poly_hkdf_sha256
                    .longterm_ecdh_keys
                    .sk
            }
            #[cfg(not(feature = "classic-mceliece"))]
            ResponderCiphersuite::X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(_) => {
                // We can never reach this because the ciphersuite can only be constructed with the feature turned on.
                unreachable!("unsupported ciphersuite")
            }
            ResponderCiphersuite::X25519NoneChaCha20Poly1305HkdfSha256(suite) => {
                &suite.longterm_ecdh_keys.sk
            }
        }
    }
    fn own_ecdh_encapsulation_key(&self) -> &DHPublicKey {
        match self {
            ResponderCiphersuite::X25519MlKem768ChaCha20Poly1305HkdfSha256(
                responder_x25519_mlkem768_chacha_poly_hkdf_sha256,
            ) => {
                &responder_x25519_mlkem768_chacha_poly_hkdf_sha256
                    .longterm_ecdh_keys
                    .pk
            }
            #[cfg(feature = "classic-mceliece")]
            ResponderCiphersuite::X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(
                responder_x25519_classic_mc_eliece_chacha_poly_hkdf_sha256,
            ) => {
                &responder_x25519_classic_mc_eliece_chacha_poly_hkdf_sha256
                    .longterm_ecdh_keys
                    .pk
            }
            #[cfg(not(feature = "classic-mceliece"))]
            ResponderCiphersuite::X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(_) => {
                // We can never reach this because the ciphersuite can only be constructed with the feature turned on.
                unreachable!("unsupported ciphersuite")
            }
            ResponderCiphersuite::X25519NoneChaCha20Poly1305HkdfSha256(
                responder_x25519_cha_cha_poly_hkdf_sha256,
            ) => {
                &responder_x25519_cha_cha_poly_hkdf_sha256
                    .longterm_ecdh_keys
                    .pk
            }
        }
    }
}
impl<'a> ResponderCiphersuite<'a> {
    pub(crate) fn own_pq_encapsulation_key(
        &self,
    ) -> Option<<Self as CiphersuiteBase>::EncapsulationKeyRef> {
        match self {
            ResponderCiphersuite::X25519MlKem768ChaCha20Poly1305HkdfSha256(
                responder_x25519_ml_kem768_cha_cha_poly_hkdf_sha256,
            ) => Some(DynamicEncapsulationKeyRef::MlKem(
                responder_x25519_ml_kem768_cha_cha_poly_hkdf_sha256.longterm_pq_encapsulation_key,
            )),
            #[cfg(feature = "classic-mceliece")]
            ResponderCiphersuite::X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(
                responder_x25519_cmc_cha_cha_poly_hkdf_sha256,
            ) => Some(DynamicEncapsulationKeyRef::CMC(
                responder_x25519_cmc_cha_cha_poly_hkdf_sha256.longterm_pq_encapsulation_key,
            )),
            #[cfg(not(feature = "classic-mceliece"))]
            ResponderCiphersuite::X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(_) => {
                // We can never reach this because the ciphersuite can only be constructed with the feature turned on.
                unreachable!("unsupported ciphersuite")
            }
            ResponderCiphersuite::X25519NoneChaCha20Poly1305HkdfSha256(_) => None,
        }
    }

    pub(crate) fn pq_decapsulate(
        &self,
        ciphertext: &<Self as CiphersuiteBase>::Ciphertext,
    ) -> Result<<Self as CiphersuiteBase>::SharedSecret, HandshakeError> {
        match self {
            ResponderCiphersuite::X25519MlKem768ChaCha20Poly1305HkdfSha256(
                responder_x25519_ml_kem768_cha_cha_poly_hkdf_sha256,
            ) => {
                let DynamicCiphertext::MlKem(inner_ctxt) = ciphertext else {
                    return Err(HandshakeError::CryptoError);
                };
                let shared_secret = libcrux_ml_kem::mlkem768::decapsulate(
                    responder_x25519_ml_kem768_cha_cha_poly_hkdf_sha256
                        .longterm_pq_decapsulation_key,
                    inner_ctxt,
                );

                Ok(DynamicSharedSecret::MlKem(shared_secret))
            }
            #[cfg(feature = "classic-mceliece")]
            ResponderCiphersuite::X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(
                responder_x25519_cmc_cha_cha_poly_hkdf_sha256,
            ) => {
                use crate::classic_mceliece::ClassicMcEliece;
                use libcrux_traits::kem::KEM;

                let DynamicCiphertext::CMC(inner_ctxt) = ciphertext else {
                    return Err(HandshakeError::CryptoError);
                };
                let shared_secret = <ClassicMcEliece as KEM>::decapsulate(
                    &responder_x25519_cmc_cha_cha_poly_hkdf_sha256
                        .longterm_pq_decapsulation_key
                        .0,
                    inner_ctxt,
                )
                .map_err(|_| HandshakeError::CryptoError)?;
                Ok(DynamicSharedSecret::CMC(shared_secret))
            }
            #[cfg(not(feature = "classic-mceliece"))]
            ResponderCiphersuite::X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(_) => {
                // We can never reach this because the ciphersuite can only be constructed with the feature turned on.
                unreachable!("unsupported ciphersuite")
            }
            ResponderCiphersuite::X25519NoneChaCha20Poly1305HkdfSha256(_) => {
                Err(HandshakeError::UnsupportedCiphersuite)
            }
        }
    }
}
