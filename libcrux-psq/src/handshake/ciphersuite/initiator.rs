use rand::CryptoRng;

#[cfg(feature = "classic-mceliece")]
use crate::classic_mceliece::PublicKey;
use crate::handshake::{
    ciphersuite::{
        traits::CiphersuiteBase,
        types::{PQCiphertext, PQEncapsulationKey, PQSharedSecret},
        CiphersuiteName,
    },
    dhkem::{DHKeyPair, DHPrivateKey, DHPublicKey},
    HandshakeError,
};

#[allow(non_camel_case_types)]
/// The ciphersuites available to a PSQ initiator in registration mode.
pub enum InitiatorCiphersuite<'a> {
    X25519NoneChaCha20Poly1305HkdfSha256(InitiatorX25519ChaCha20Poly1305HkdfSha256<'a>),
    X25519MlKem768ChaCha20Poly1305HkdfSha256(InitiatorX25519Mlkem768ChaCha20Poly1305HkdfSha256<'a>),
    #[cfg(feature = "classic-mceliece")]
    X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(
        InitiatorX25519ClassicMcElieceChaCha20Poly1305HkdfSha256<'a>,
    ),
    #[cfg(not(feature = "classic-mceliece"))]
    X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(std::marker::PhantomData<&'a [u8]>),
}

impl<'a> CiphersuiteBase for InitiatorCiphersuite<'a> {
    type Ciphertext = PQCiphertext;
    type EncapsulationKeyRef = PQEncapsulationKey<'a>;
    type SharedSecret = PQSharedSecret<'a>;

    fn name(&self) -> CiphersuiteName {
        match self {
            InitiatorCiphersuite::X25519NoneChaCha20Poly1305HkdfSha256(_) => {
                CiphersuiteName::X25519_NONE_CHACHA20POLY1305_HKDFSHA256
            }
            InitiatorCiphersuite::X25519MlKem768ChaCha20Poly1305HkdfSha256(_) => {
                CiphersuiteName::X25519_MLKEM768_CHACHA20POLY1305_HKDFSHA256
            }
            #[cfg(feature = "classic-mceliece")]
            InitiatorCiphersuite::X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(_) => {
                CiphersuiteName::X25519_CLASSICMCELIECE_CHACHA20POLY1305_HKDFSHA256
            }
            #[cfg(not(feature = "classic-mceliece"))]
            InitiatorCiphersuite::X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(_) => {
                // We can never reach this because the ciphersuite can only be constructed with the feature turned on.
                unreachable!("unsupported ciphersuite")
            }
        }
    }

    fn own_ecdh_decapsulation_key(&self) -> &DHPrivateKey {
        match self {
            InitiatorCiphersuite::X25519NoneChaCha20Poly1305HkdfSha256(
                initiator_x25519_chacha_poly_hkdf_sha256,
            ) => {
                &initiator_x25519_chacha_poly_hkdf_sha256
                    .longterm_ecdh_keys
                    .sk
            }
            InitiatorCiphersuite::X25519MlKem768ChaCha20Poly1305HkdfSha256(
                initiator_x25519_mlkem768_chacha_poly_hkdf_sha256,
            ) => {
                &initiator_x25519_mlkem768_chacha_poly_hkdf_sha256
                    .longterm_ecdh_keys
                    .sk
            }
            #[cfg(feature = "classic-mceliece")]
            InitiatorCiphersuite::X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(
                initiator_x25519_classic_mc_eliece_chacha_poly_hkdf_sha256,
            ) => {
                &initiator_x25519_classic_mc_eliece_chacha_poly_hkdf_sha256
                    .longterm_ecdh_keys
                    .sk
            }

            #[cfg(not(feature = "classic-mceliece"))]
            InitiatorCiphersuite::X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(_) => {
                // We can never reach this because the ciphersuite can only be constructed with the feature turned on.
                unreachable!("unsupported ciphersuite")
            }
        }
    }

    fn own_ecdh_encapsulation_key(&self) -> &DHPublicKey {
        match self {
            InitiatorCiphersuite::X25519NoneChaCha20Poly1305HkdfSha256(
                initiator_x25519_chacha_poly_hkdf_sha256,
            ) => {
                &initiator_x25519_chacha_poly_hkdf_sha256
                    .longterm_ecdh_keys
                    .pk
            }
            InitiatorCiphersuite::X25519MlKem768ChaCha20Poly1305HkdfSha256(
                initiator_x25519_mlkem768_chacha_poly_hkdf_sha256,
            ) => {
                &initiator_x25519_mlkem768_chacha_poly_hkdf_sha256
                    .longterm_ecdh_keys
                    .pk
            }
            #[cfg(feature = "classic-mceliece")]
            InitiatorCiphersuite::X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(
                initiator_x25519_classic_mc_eliece_chacha_poly_hkdf_sha256,
            ) => {
                &initiator_x25519_classic_mc_eliece_chacha_poly_hkdf_sha256
                    .longterm_ecdh_keys
                    .pk
            }
            #[cfg(not(feature = "classic-mceliece"))]
            InitiatorCiphersuite::X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(_) => {
                // We can never reach this because the ciphersuite can only be constructed with the feature turned on.
                unreachable!("unsupported ciphersuite")
            }
        }
    }
}

pub(crate) type PQOptionPair<A, B> = (Option<A>, Option<B>);

impl<'a> InitiatorCiphersuite<'a> {
    pub(crate) fn peer_pq_encapsulation_key(
        &self,
    ) -> Option<<Self as CiphersuiteBase>::EncapsulationKeyRef> {
        match self {
            InitiatorCiphersuite::X25519NoneChaCha20Poly1305HkdfSha256(_) => None,
            InitiatorCiphersuite::X25519MlKem768ChaCha20Poly1305HkdfSha256(
                initiator_x25519_mlkem768_chacha_poly_hkdf_sha256,
            ) => Some(PQEncapsulationKey::MlKem(
                initiator_x25519_mlkem768_chacha_poly_hkdf_sha256.peer_longterm_mlkem_pk,
            )),
            #[cfg(feature = "classic-mceliece")]
            InitiatorCiphersuite::X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(
                initiator_x25519_classic_mc_eliece_chacha_poly_hkdf_sha256,
            ) => Some(PQEncapsulationKey::CMC(
                initiator_x25519_classic_mc_eliece_chacha_poly_hkdf_sha256.peer_longterm_cmc_pk,
            )),
            #[cfg(not(feature = "classic-mceliece"))]
            InitiatorCiphersuite::X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(_) => {
                // We can never reach this because the ciphersuite can only be constructed with the feature turned on.
                unreachable!("unsupported ciphersuite")
            }
        }
    }

    pub(crate) fn peer_ecdh_encapsulation_key(&self) -> &DHPublicKey {
        match self {
            InitiatorCiphersuite::X25519NoneChaCha20Poly1305HkdfSha256(
                initiator_x25519_chacha_poly_hkdf_sha256,
            ) => initiator_x25519_chacha_poly_hkdf_sha256.peer_longterm_ecdh_pk,
            InitiatorCiphersuite::X25519MlKem768ChaCha20Poly1305HkdfSha256(
                initiator_x25519_mlkem768_chacha_poly_hkdf_sha256,
            ) => initiator_x25519_mlkem768_chacha_poly_hkdf_sha256.peer_longterm_ecdh_pk,
            #[cfg(feature = "classic-mceliece")]
            InitiatorCiphersuite::X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(
                initiator_x25519_classic_mc_eliece_chacha_poly_hkdf_sha256,
            ) => initiator_x25519_classic_mc_eliece_chacha_poly_hkdf_sha256.peer_longterm_ecdh_pk,
            #[cfg(not(feature = "classic-mceliece"))]
            InitiatorCiphersuite::X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(_) => {
                // We can never reach this because the ciphersuite can only be constructed with the feature turned on.
                unreachable!("unsupported ciphersuite")
            }
        }
    }

    pub(crate) fn is_pq(&self) -> bool {
        match self {
            InitiatorCiphersuite::X25519NoneChaCha20Poly1305HkdfSha256(_) => false,
            InitiatorCiphersuite::X25519MlKem768ChaCha20Poly1305HkdfSha256(_) => true,
            #[cfg(feature = "classic-mceliece")]
            InitiatorCiphersuite::X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(_) => true,
            #[cfg(not(feature = "classic-mceliece"))]
            InitiatorCiphersuite::X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(_) => {
                // We can never reach this because the ciphersuite can only be constructed with the feature turned on.
                unreachable!("unsupported ciphersuite")
            }
        }
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
        match self {
            InitiatorCiphersuite::X25519NoneChaCha20Poly1305HkdfSha256(_) => Ok((None, None)),
            InitiatorCiphersuite::X25519MlKem768ChaCha20Poly1305HkdfSha256(
                initiator_x25519_mlkem768_chacha_poly_hkdf_sha256,
            ) => {
                let mut rand = [0u8; libcrux_ml_kem::ENCAPS_SEED_SIZE];
                rng.fill_bytes(&mut rand);
                let (ct, ss) = libcrux_ml_kem::mlkem768::encapsulate(
                    initiator_x25519_mlkem768_chacha_poly_hkdf_sha256.peer_longterm_mlkem_pk,
                    rand,
                );

                Ok((
                    Some(PQCiphertext::MlKem(Box::new(ct))),
                    Some(PQSharedSecret::MlKem(ss)),
                ))
            }
            #[cfg(feature = "classic-mceliece")]
            InitiatorCiphersuite::X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(
                initiator_x25519_classic_mc_eliece_chacha_poly_hkdf_sha256,
            ) => {
                use crate::classic_mceliece::ClassicMcEliece;
                use libcrux_traits::kem::KEM;

                let (ss, ct) = <ClassicMcEliece as KEM>::encapsulate(
                    initiator_x25519_classic_mc_eliece_chacha_poly_hkdf_sha256.peer_longterm_cmc_pk,
                    rng,
                )
                .map_err(|_| HandshakeError::CryptoError)?;

                Ok((
                    Some(PQCiphertext::CMC(Box::new(ct))),
                    Some(PQSharedSecret::CMC(ss)),
                ))
            }

            #[cfg(not(feature = "classic-mceliece"))]
            InitiatorCiphersuite::X25519ClassicMcElieceChaCha20Poly1305HkdfSha256(_) => {
                // We can never reach this because the ciphersuite can only be constructed with the feature turned on.
                unreachable!("unsupported ciphersuite")
            }
        }
    }
}

pub struct InitiatorX25519Mlkem768ChaCha20Poly1305HkdfSha256<'a> {
    pub longterm_ecdh_keys: &'a DHKeyPair,
    pub peer_longterm_ecdh_pk: &'a DHPublicKey,
    pub peer_longterm_mlkem_pk: &'a libcrux_ml_kem::mlkem768::MlKem768PublicKey,
}
pub struct InitiatorX25519ChaCha20Poly1305HkdfSha256<'a> {
    pub longterm_ecdh_keys: &'a DHKeyPair,
    pub peer_longterm_ecdh_pk: &'a DHPublicKey,
}

#[cfg(feature = "classic-mceliece")]
pub struct InitiatorX25519ClassicMcElieceChaCha20Poly1305HkdfSha256<'a> {
    pub longterm_ecdh_keys: &'a DHKeyPair,
    pub peer_longterm_ecdh_pk: &'a DHPublicKey,
    pub peer_longterm_cmc_pk: &'a PublicKey,
}
