use libcrux_kem::{MlKem768PrivateKey, MlKem768PublicKey};
use tls_codec::SerializeBytes;

#[cfg(feature = "classic-mceliece")]
use crate::classic_mceliece::{PublicKey, SecretKey};
use crate::handshake::{
    ciphersuite::{
        traits::CiphersuiteBase,
        types::{PQCiphertext, PQEncapsulationKey, PQSharedSecret},
        CiphersuiteName,
    },
    dhkem::DHKeyPair,
    transcript::Transcript,
    types::{SigVerificationKey, Signature},
    HandshakeError,
};

pub(crate) enum PqKemKeyPair<'a> {
    None,
    MlKem(&'a MlKem768PrivateKey, &'a MlKem768PublicKey),
    #[cfg(feature = "classic-mceliece")]
    CMC(&'a SecretKey, &'a PublicKey),
    #[cfg(not(feature = "classic-mceliece"))]
    #[allow(unused)]
    CMC(
        std::marker::PhantomData<&'a [u8]>,
        std::marker::PhantomData<&'a [u8]>,
    ),
}

impl<'a> PqKemKeyPair<'a> {
    pub(crate) fn encapsulation_key(&self) -> Option<PQEncapsulationKey<'a>> {
        match self {
            PqKemKeyPair::None => None,
            PqKemKeyPair::MlKem(_, ml_kem_public_key) => {
                Some(PQEncapsulationKey::MlKem(ml_kem_public_key))
            }
            #[cfg(feature = "classic-mceliece")]
            PqKemKeyPair::CMC(_, public_key) => Some(PQEncapsulationKey::CMC(public_key)),
            #[cfg(not(feature = "classic-mceliece"))]
            PqKemKeyPair::CMC(_, _) => {
                // We can never reach this because the ciphersuite can only be constructed with the feature turned on.
                unreachable!("unsupported ciphersuite")
            }
        }
    }
}

impl<'a> From<(&'a MlKem768PrivateKey, &'a MlKem768PublicKey)> for PqKemKeyPair<'a> {
    fn from(value: (&'a MlKem768PrivateKey, &'a MlKem768PublicKey)) -> Self {
        PqKemKeyPair::MlKem(value.0, value.1)
    }
}

#[cfg(feature = "classic-mceliece")]
impl<'a> From<(&'a SecretKey, &'a PublicKey)> for PqKemKeyPair<'a> {
    fn from(value: (&'a SecretKey, &'a PublicKey)) -> Self {
        PqKemKeyPair::CMC(value.0, value.1)
    }
}

pub struct ResponderCiphersuite<'a> {
    pub(crate) name: CiphersuiteName,
    pub(crate) kex: &'a DHKeyPair,
    pub(crate) pq: PqKemKeyPair<'a>,
}

impl<'a> CiphersuiteBase for ResponderCiphersuite<'a> {
    type Ciphertext = PQCiphertext;
    type EncapsulationKeyRef = PQEncapsulationKey<'a>;
    type SharedSecret = PQSharedSecret;

    fn name(&self) -> CiphersuiteName {
        self.name
    }

    // fn tx0(&self, ctx: &[u8], peer_pk: &DHPublicKey) -> Result<Transcript, HandshakeError> {
    //     todo!()
    //     // match self {
    //     //     ResponderCiphersuite::X25519NoneChaCha20Poly1305HkdfSha256(x) => {
    //     //         transcript::tx0(ctx, &x.longterm_ecdh_keys.pk, peer_pk)
    //     //     }
    //     //     ResponderCiphersuite::X25519MlKem768ChaCha20Poly1305HkdfSha256(x) => {
    //     //         transcript::tx0(ctx, &x.longterm_ecdh_keys.pk, peer_pk)
    //     //     }
    //     //     #[cfg(feature = "classic-mceliece")]
    //     //     ResponderCiphersuite::X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(x) => {
    //     //         transcript::tx0(ctx, &x.longterm_ecdh_keys.pk, peer_pk)
    //     //     }
    //     //     #[cfg(not(feature = "classic-mceliece"))]
    //     //     ResponderCiphersuite::X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(_) => {
    //     //         // We can never reach this because the ciphersuite can only be constructed with the feature turned on.
    //     //         unreachable!("unsupported ciphersuite")
    //     //     }
    //     // }
    // }

    // fn tx1(&self, tx0: &Transcript, pq_encapsulation: &[u8]) -> Result<Transcript, HandshakeError> {
    //     todo!()
    // }

    // fn k0(&self, tx0: Transcript, peer_pk: &DHPublicKey) -> Result<AEADKey, HandshakeError> {
    //     todo!()
    //     // struct K0Ikm<'a> {
    //     //     g_xs: &'a DHSharedSecret,
    //     // }
    //     // let own_sk = match self {
    //     //     ResponderCiphersuite::X25519NoneChaCha20Poly1305HkdfSha256(x) => {
    //     //         &x.longterm_ecdh_keys.sk
    //     //     }
    //     //     ResponderCiphersuite::X25519MlKem768ChaCha20Poly1305HkdfSha256(x) => {
    //     //         &x.longterm_ecdh_keys.sk
    //     //     }
    //     //     #[cfg(feature = "classic-mceliece")]
    //     //     ResponderCiphersuite::X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(x) => {
    //     //         &x.longterm_ecdh_keys.sk
    //     //     }
    //     //     #[cfg(feature = "classic-mceliece")]
    //     //     ResponderCiphersuite::X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(_) => {
    //     //         // We can never reach this because the ciphersuite can only be constructed with the feature turned on.
    //     //         unreachable!("unsupported ciphersuite")
    //     //     }
    //     // };

    //     // let ikm = K0Ikm {
    //     //     g_xs: &DHSharedSecret::derive(own_sk, peer_pk)?,
    //     // };

    //     // Ok(AEADKey::new(&ikm, &tx0)?)
    // }

    // fn k1(&self) -> Result<AEADKey, HandshakeError> {
    //     todo!()
    // }

    // fn tx2(&self) -> Result<Transcript, HandshakeError> {
    //     todo!()
    // }

    // fn k2(&self) -> Result<AEADKey, HandshakeError> {
    //     todo!()
    // }

    // fn client_authenticator(&self) -> super::types::Authenticator {
    //     todo!()
    // }
}
impl<'a> ResponderCiphersuite<'a> {
    pub(crate) fn verify(
        &self,
        vk: &SigVerificationKey,
        tx1: &Transcript,
        signature: &Signature,
    ) -> Result<(), HandshakeError> {
        let payload = tx1.tls_serialize().map_err(HandshakeError::Serialize)?;
        match (vk, signature) {
            (SigVerificationKey::Ed25519(verification_key), Signature::Ed25519(sig)) => {
                libcrux_ed25519::verify(&payload, verification_key.as_ref(), sig)
                    .map_err(|e| e.into())
            }

            (
                SigVerificationKey::MlDsa65(mldsaverification_key),
                Signature::MlDsa65(mldsasignature),
            ) => libcrux_ml_dsa::ml_dsa_65::verify(
                mldsaverification_key,
                &payload,
                b"PSQ",
                mldsasignature,
            )
            .map_err(|e| e.into()),
            (SigVerificationKey::Ed25519(_), Signature::MlDsa65(_))
            | (SigVerificationKey::MlDsa65(_), Signature::Ed25519(_)) => {
                Err(HandshakeError::UnsupportedCiphersuite)
            }
        }
    }

    pub(crate) fn own_pq_encapsulation_key(
        &self,
    ) -> Option<<Self as CiphersuiteBase>::EncapsulationKeyRef> {
        match self.pq {
            PqKemKeyPair::None => None,
            PqKemKeyPair::MlKem(_, ml_kem_public_key) => {
                Some(PQEncapsulationKey::MlKem(ml_kem_public_key))
            }
            #[cfg(feature = "classic-mceliece")]
            PqKemKeyPair::CMC(_, public_key) => Some(PQEncapsulationKey::CMC(public_key)),
            #[cfg(not(feature = "classic-mceliece"))]
            PqKemKeyPair::CMC(_, _) => {
                // We can never reach this because the ciphersuite can only be constructed with the feature turned on.
                unreachable!("unsupported ciphersuite")
            }
        }
    }

    pub(crate) fn pq_decapsulate(
        &self,
        ciphertext: &<Self as CiphersuiteBase>::Ciphertext,
    ) -> Result<<Self as CiphersuiteBase>::SharedSecret, HandshakeError> {
        match self.pq {
            PqKemKeyPair::None => Err(HandshakeError::UnsupportedCiphersuite),
            PqKemKeyPair::MlKem(ml_kem_private_key, _) => {
                let PQCiphertext::MlKem(inner_ctxt) = ciphertext else {
                    return Err(HandshakeError::CryptoError);
                };
                let shared_secret =
                    libcrux_ml_kem::mlkem768::decapsulate(ml_kem_private_key, inner_ctxt);

                Ok(PQSharedSecret::MlKem(shared_secret))
            }
            #[cfg(feature = "classic-mceliece")]
            PqKemKeyPair::CMC(secret_key, _) => {
                use crate::classic_mceliece::ClassicMcEliece;
                use libcrux_traits::kem::KEM;

                let PQCiphertext::CMC(inner_ctxt) = ciphertext else {
                    return Err(HandshakeError::CryptoError);
                };
                let shared_secret =
                    <ClassicMcEliece as KEM>::decapsulate(&secret_key.0, inner_ctxt)
                        .map_err(|_| HandshakeError::CryptoError)?;
                Ok(PQSharedSecret::CMC(shared_secret))
            }
            #[cfg(not(feature = "classic-mceliece"))]
            PqKemKeyPair::CMC(_, _) => {
                // We can never reach this because the ciphersuite can only be constructed with the feature turned on.
                unreachable!("unsupported ciphersuite")
            }
        }
    }
}
