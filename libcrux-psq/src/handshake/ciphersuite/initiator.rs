use libcrux_ed25519::{SigningKey, VerificationKey};
use libcrux_ml_dsa::ml_dsa_65::{MLDSA65SigningKey, MLDSA65VerificationKey};
use rand::CryptoRng;
use tls_codec::SerializeBytes;

#[cfg(feature = "classic-mceliece")]
use crate::classic_mceliece::PublicKey;
use crate::handshake::{
    ciphersuite::{
        traits::CiphersuiteBase,
        types::{PQCiphertext, PQEncapsulationKey, PQSharedSecret},
        CiphersuiteName,
    },
    dhkem::{DHKeyPair, DHPublicKey},
    transcript::Transcript,
    types::{SigVerificationKey, Signature},
    HandshakeError,
};

#[derive(Clone, Copy)]
pub(crate) enum PqKemPublicKey<'a> {
    None,
    MlKem(&'a libcrux_ml_kem::mlkem768::MlKem768PublicKey),
    #[cfg(feature = "classic-mceliece")]
    CMC(&'a PublicKey),
    #[cfg(not(feature = "classic-mceliece"))]
    #[allow(unused)]
    CMC(std::marker::PhantomData<&'a [u8]>),
}

impl<'a> From<&'a libcrux_ml_kem::mlkem768::MlKem768PublicKey> for PqKemPublicKey<'a> {
    fn from(value: &'a libcrux_ml_kem::mlkem768::MlKem768PublicKey) -> Self {
        PqKemPublicKey::MlKem(value)
    }
}

#[cfg(feature = "classic-mceliece")]
impl<'a> From<&'a PublicKey> for PqKemPublicKey<'a> {
    fn from(value: &'a PublicKey) -> Self {
        PqKemPublicKey::CMC(value)
    }
}

#[derive(Clone, Copy)]
pub(crate) enum SigAuth<'a> {
    Ed25519(&'a SigningKey, &'a VerificationKey),
    MlDsa65(&'a MLDSA65SigningKey, &'a MLDSA65VerificationKey),
}

impl From<SigAuth<'_>> for SigVerificationKey {
    fn from(value: SigAuth<'_>) -> Self {
        match value {
            SigAuth::Ed25519(_, verification_key) => {
                SigVerificationKey::Ed25519(verification_key.clone())
            }
            SigAuth::MlDsa65(_, mldsaverification_key) => {
                SigVerificationKey::MlDsa65(mldsaverification_key.clone())
            }
        }
    }
}

impl<'a> From<PqKemPublicKey<'a>> for Option<PQEncapsulationKey<'a>> {
    fn from(value: PqKemPublicKey<'a>) -> Self {
        match value {
            PqKemPublicKey::None => None,
            PqKemPublicKey::MlKem(ml_kem_public_key) => {
                Some(PQEncapsulationKey::MlKem(ml_kem_public_key))
            }
            #[cfg(feature = "classic-mceliece")]
            PqKemPublicKey::CMC(public_key) => Some(PQEncapsulationKey::CMC(public_key)),
            #[cfg(not(feature = "classic-mceliece"))]
            PqKemPublicKey::CMC(_) => {
                // We can never reach this because the ciphersuite can only be constructed with the feature turned on.
                unreachable!("unsupported ciphersuite")
            }
        }
    }
}

#[derive(Clone, Copy)]
pub(crate) enum Auth<'a> {
    DH(&'a DHKeyPair),
    Sig(SigAuth<'a>),
}

impl<'a> From<&'a DHKeyPair> for Auth<'a> {
    fn from(value: &'a DHKeyPair) -> Self {
        Auth::DH(value)
    }
}
impl<'a> From<(&'a SigningKey, &'a VerificationKey)> for Auth<'a> {
    fn from(value: (&'a SigningKey, &'a VerificationKey)) -> Self {
        Auth::Sig(SigAuth::Ed25519(value.0, value.1))
    }
}
impl<'a> From<(&'a MLDSA65SigningKey, &'a MLDSA65VerificationKey)> for Auth<'a> {
    fn from(value: (&'a MLDSA65SigningKey, &'a MLDSA65VerificationKey)) -> Self {
        Auth::Sig(SigAuth::MlDsa65(value.0, value.1))
    }
}

pub struct InitiatorCiphersuite<'a> {
    pub(crate) name: CiphersuiteName,
    pub(crate) kex: &'a DHPublicKey,
    pub(crate) pq: PqKemPublicKey<'a>,
    pub(crate) auth: Auth<'a>,
}

impl<'a> CiphersuiteBase for InitiatorCiphersuite<'a> {
    type Ciphertext = PQCiphertext;
    type EncapsulationKeyRef = PQEncapsulationKey<'a>;
    type SharedSecret = PQSharedSecret;

    fn name(&self) -> CiphersuiteName {
        self.name
    }
}

pub(crate) type PQOptionPair<A, B> = (Option<A>, Option<B>);

impl<'a> InitiatorCiphersuite<'a> {
    pub(crate) fn sign(
        &self,
        rng: &mut impl CryptoRng,
        tx: &Transcript,
    ) -> Result<Signature, HandshakeError> {
        match self.auth {
            Auth::DH(_dhkey_pair) => Err(HandshakeError::UnsupportedCiphersuite),
            Auth::Sig(sig_auth) => {
                let payload = tx.tls_serialize().map_err(HandshakeError::Serialize)?;
                match sig_auth {
                    SigAuth::Ed25519(signing_key, _) => {
                        let sig = libcrux_ed25519::sign(&payload, signing_key.as_ref())?;
                        Ok(Signature::Ed25519(sig))
                    }
                    SigAuth::MlDsa65(mldsasigning_key, _) => {
                        let mut randomness = [0u8; libcrux_ml_dsa::SIGNING_RANDOMNESS_SIZE];
                        rng.fill_bytes(&mut randomness);
                        let sig = libcrux_ml_dsa::ml_dsa_65::sign(
                            mldsasigning_key,
                            &payload,
                            b"PSQ",
                            randomness,
                        )?;
                        Ok(Signature::MlDsa65(sig))
                    }
                }
            }
        }
    }
    pub(crate) fn peer_pq_encapsulation_key(
        &self,
    ) -> Option<<Self as CiphersuiteBase>::EncapsulationKeyRef> {
        match self.pq {
            PqKemPublicKey::None => None,
            PqKemPublicKey::MlKem(ml_kem_public_key) => {
                Some(PQEncapsulationKey::MlKem(ml_kem_public_key))
            }
            #[cfg(feature = "classic-mceliece")]
            PqKemPublicKey::CMC(public_key) => Some(PQEncapsulationKey::CMC(public_key)),
            #[cfg(not(feature = "classic-mceliece"))]
            PqKemPublicKey::CMC(_) => {
                // We can never reach this because the ciphersuite can only be constructed with the feature turned on.
                unreachable!("unsupported ciphersuite")
            }
        }
    }

    pub(crate) fn peer_ecdh_encapsulation_key(&self) -> &DHPublicKey {
        self.kex
    }

    pub(crate) fn is_pq(&self) -> bool {
        !matches!(self.pq, PqKemPublicKey::None)
    }

    pub(crate) fn pq_encapsulate(
        &self,
        rng: &mut impl CryptoRng,
    ) -> Result<
        PQOptionPair<
            <Self as CiphersuiteBase>::Ciphertext,
            <Self as CiphersuiteBase>::SharedSecret,
        >,
        HandshakeError,
    > {
        match self.pq {
            PqKemPublicKey::None => Ok((None, None)),
            PqKemPublicKey::MlKem(ml_kem_public_key) => {
                let mut rand = [0u8; libcrux_ml_kem::ENCAPS_SEED_SIZE];
                rng.fill_bytes(&mut rand);
                let (ct, ss) = libcrux_ml_kem::mlkem768::encapsulate(ml_kem_public_key, rand);

                Ok((
                    Some(PQCiphertext::MlKem(Box::new(ct))),
                    Some(PQSharedSecret::MlKem(ss)),
                ))
            }
            #[cfg(feature = "classic-mceliece")]
            PqKemPublicKey::CMC(public_key) => {
                use crate::classic_mceliece::ClassicMcEliece;
                use libcrux_traits::kem::KEM;

                let (ss, ct) = <ClassicMcEliece as KEM>::encapsulate(public_key, rng)
                    .map_err(|_| HandshakeError::CryptoError)?;

                Ok((
                    Some(PQCiphertext::CMC(Box::new(ct))),
                    Some(PQSharedSecret::CMC(ss)),
                ))
            }
            #[cfg(not(feature = "classic-mceliece"))]
            PqKemPublicKey::CMC(_) => {
                // We can never reach this because the ciphersuite can only be constructed with the feature turned on.
                unreachable!("unsupported ciphersuite")
            }
        }
    }
}
