use libcrux_kem::{MlKem768Ciphertext, MlKem768PrivateKey, MlKem768PublicKey};
use libcrux_ml_kem::MlKemSharedSecret;
use rand::CryptoRng;
use tls_codec::{
    Deserialize, Serialize, SerializeBytes, Size, TlsDeserialize, TlsSerialize, TlsSerializeBytes,
    TlsSize,
};

#[cfg(feature = "classic-mceliece")]
use crate::classic_mceliece::{Ciphertext, PublicKey, SecretKey, SharedSecret};
use crate::handshake::{
    dhkem::{DHKeyPair, DHPrivateKey, DHPublicKey},
    HandshakeError,
};

#[derive(Clone, Copy, Debug)]
/// Available ciphersuites for use in the PSQ handshake.
pub enum CiphersuiteName {
    /// Use X25519 for the outer KEM, no inner KEM, Chacha20Poly1305 as payload AEAD and SHA-256 for HKDF.
    X25519ChachaPolyHkdfSha256,
    /// Use X25519 for the outer KEM, ML-KEM 768 for the inner KEM, Chacha20Poly1305 as payload AEAD and SHA-256 for HKDF.
    X25519Mlkem768ChachaPolyHkdfSha256,
    /// Use X25519 for the outer KEM, Classic McEliece for the inner KEM, Chacha20Poly1305 as payload AEAD and SHA-256 for HKDF. (requires feature `classic-mceliece`)
    X25519ClassicMcElieceChachaPolyHkdfSha256,
}

/// A builder for PSQ handshake ciphersuites.
pub struct CiphersuiteBuilder<'a> {
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

#[allow(non_camel_case_types)]
/// The ciphersuites available to a PSQ initiator in registration mode.
pub enum InitiatorCiphersuite<'a> {
    X25519_ChaChaPoly_HkdfSha256(InitiatorX25519ChachaPolyHkdfSha256<'a>),
    X25519_MlKem768_ChaChaPoly_HkdfSha256(InitiatorX25519Mlkem768ChachaPolyHkdfSha256<'a>),
    #[cfg(feature = "classic-mceliece")]
    X25519_ClassicMcEliece_ChaChaPoly_HkdfSha256(
        InitiatorX25519ClassicMcElieceChachaPolyHkdfSha256<'a>,
    ),
    #[cfg(not(feature = "classic-mceliece"))]
    X25519_ClassicMcEliece_ChaChaPoly_HkdfSha256(DummyCiphersuite),
}

#[allow(non_camel_case_types)]
/// The ciphersuites available to a PSQ responder.
pub enum ResponderCiphersuite<'a> {
    X25519_ChaChaPoly_HkdfSha256(ResponderX25519ChaChaPolyHkdfSha256<'a>),
    X25519_MlKem768_ChaChaPoly_HkdfSha256(ResponderX25519MlKem768ChaChaPolyHkdfSha256<'a>),
    #[cfg(feature = "classic-mceliece")]
    X25519_ClassicMcEliece_ChaChaPoly_HkdfSha256(
        ResponderX25519ClassicMcElieceChaChaPolyHkdfSha256<'a>,
    ),
    #[cfg(not(feature = "classic-mceliece"))]
    X25519_ClassicMcEliece_ChaChaPoly_HkdfSha256(DummyCiphersuite),
}
pub struct DummyCiphersuite;

#[derive(TlsSize, TlsDeserialize, TlsSerialize, TlsSerializeBytes)]
pub struct Dummy;

impl CiphersuiteBase for DummyCiphersuite {
    type Ciphertext = Dummy;

    type EncapsulationKeyRef = Dummy;

    type SharedSecret = Dummy;

    fn name(&self) -> CiphersuiteName {
        unreachable!("this should never be called")
    }

    fn own_ecdh_decapsulation_key(&self) -> &DHPrivateKey {
        unreachable!("this should never be called")
    }

    fn own_ecdh_encapsulation_key(&self) -> &DHPublicKey {
        unreachable!("this should never be called")
    }
}

#[derive(TlsSize, TlsDeserialize, TlsSerialize)]
#[repr(u8)]
pub enum DynamicCiphertext {
    MlKem(MlKem768Ciphertext),
    #[cfg(feature = "classic-mceliece")]
    CMC(Ciphertext),
    #[cfg(not(feature = "classic-mceliece"))]
    CMC,
}

#[derive(TlsSize, TlsSerialize)]
#[repr(u8)]
pub enum DynamicEncapsulationKeyRef<'a> {
    MlKem(&'a MlKem768PublicKey),
    #[cfg(feature = "classic-mceliece")]
    CMC(&'a PublicKey),
    #[cfg(not(feature = "classic-mceliece"))]
    CMC,
}

impl<'a> From<&'a MlKem768PublicKey> for DynamicEncapsulationKeyRef<'a> {
    fn from(value: &'a MlKem768PublicKey) -> Self {
        Self::MlKem(value)
    }
}

#[cfg(feature = "classic-mceliece")]
impl<'a> From<&'a PublicKey> for DynamicEncapsulationKeyRef<'a> {
    fn from(value: &'a PublicKey) -> Self {
        Self::CMC(value)
    }
}

#[derive(TlsSize, TlsSerializeBytes)]
#[repr(u8)]
pub enum DynamicSharedSecret<'a> {
    None,
    MlKem(MlKemSharedSecret),
    #[cfg(feature = "classic-mceliece")]
    CMC(SharedSecret<'a>),
    #[cfg(not(feature = "classic-mceliece"))]
    CMC(std::marker::PhantomData<&'a [u8]>),
}

pub enum DynamicDecapsulationKey {
    None,
    MlKem(MlKem768PrivateKey),
    #[cfg(feature = "classic-mceliece")]
    CMC(SecretKey),
    #[cfg(not(feature = "classic-mceliece"))]
    CMC,
}

pub trait CiphersuiteBase {
    type Ciphertext: Serialize + Deserialize + Size;
    type EncapsulationKeyRef: Serialize + Size;
    type SharedSecret: SerializeBytes + Size;

    fn name(&self) -> CiphersuiteName;

    fn own_ecdh_decapsulation_key(&self) -> &DHPrivateKey;
    fn own_ecdh_encapsulation_key(&self) -> &DHPublicKey;
}

impl<'a> CiphersuiteBase for ResponderCiphersuite<'a> {
    type Ciphertext = DynamicCiphertext;
    type EncapsulationKeyRef = DynamicEncapsulationKeyRef<'a>;
    type SharedSecret = DynamicSharedSecret<'a>;

    fn name(&self) -> CiphersuiteName {
        match self {
            ResponderCiphersuite::X25519_MlKem768_ChaChaPoly_HkdfSha256(_) => {
                CiphersuiteName::X25519Mlkem768ChachaPolyHkdfSha256
            }
            #[cfg(feature = "classic-mceliece")]
            ResponderCiphersuite::X25519_ClassicMcEliece_ChaChaPoly_HkdfSha256(_) => {
                CiphersuiteName::X25519ClassicMcElieceChachaPolyHkdfSha256
            }
            #[cfg(not(feature = "classic-mceliece"))]
            ResponderCiphersuite::X25519_ClassicMcEliece_ChaChaPoly_HkdfSha256(_) => {
                panic!("unsupported ciphersuite")
            }
            ResponderCiphersuite::X25519_ChaChaPoly_HkdfSha256(_) => {
                CiphersuiteName::X25519ChachaPolyHkdfSha256
            }
        }
    }

    fn own_ecdh_decapsulation_key(&self) -> &DHPrivateKey {
        match self {
            ResponderCiphersuite::X25519_MlKem768_ChaChaPoly_HkdfSha256(
                responder_x25519_mlkem768_chacha_poly_hkdf_sha256,
            ) => {
                &responder_x25519_mlkem768_chacha_poly_hkdf_sha256
                    .longterm_ecdh_keys
                    .sk
            }
            #[cfg(feature = "classic-mceliece")]
            ResponderCiphersuite::X25519_ClassicMcEliece_ChaChaPoly_HkdfSha256(
                responder_x25519_classic_mc_eliece_chacha_poly_hkdf_sha256,
            ) => {
                &responder_x25519_classic_mc_eliece_chacha_poly_hkdf_sha256
                    .longterm_ecdh_keys
                    .sk
            }
            #[cfg(not(feature = "classic-mceliece"))]
            ResponderCiphersuite::X25519_ClassicMcEliece_ChaChaPoly_HkdfSha256(_) => {
                panic!("unsupported ciphersuite")
            }
            ResponderCiphersuite::X25519_ChaChaPoly_HkdfSha256(suite) => {
                &suite.longterm_ecdh_keys.sk
            }
        }
    }

    fn own_ecdh_encapsulation_key(&self) -> &DHPublicKey {
        match self {
            ResponderCiphersuite::X25519_MlKem768_ChaChaPoly_HkdfSha256(
                responder_x25519_mlkem768_chacha_poly_hkdf_sha256,
            ) => {
                &responder_x25519_mlkem768_chacha_poly_hkdf_sha256
                    .longterm_ecdh_keys
                    .pk
            }
            #[cfg(feature = "classic-mceliece")]
            ResponderCiphersuite::X25519_ClassicMcEliece_ChaChaPoly_HkdfSha256(
                responder_x25519_classic_mc_eliece_chacha_poly_hkdf_sha256,
            ) => {
                &responder_x25519_classic_mc_eliece_chacha_poly_hkdf_sha256
                    .longterm_ecdh_keys
                    .pk
            }
            #[cfg(not(feature = "classic-mceliece"))]
            ResponderCiphersuite::X25519_ClassicMcEliece_ChaChaPoly_HkdfSha256(_) => {
                panic!("unsupported ciphersuite")
            }
            ResponderCiphersuite::X25519_ChaChaPoly_HkdfSha256(
                responder_x25519_cha_cha_poly_hkdf_sha256,
            ) => {
                &responder_x25519_cha_cha_poly_hkdf_sha256
                    .longterm_ecdh_keys
                    .pk
            }
        }
    }
}
impl<'a> CiphersuiteBase for InitiatorCiphersuite<'a> {
    type Ciphertext = DynamicCiphertext;
    type EncapsulationKeyRef = DynamicEncapsulationKeyRef<'a>;
    type SharedSecret = DynamicSharedSecret<'a>;

    fn name(&self) -> CiphersuiteName {
        match self {
            InitiatorCiphersuite::X25519_ChaChaPoly_HkdfSha256(_) => {
                CiphersuiteName::X25519ChachaPolyHkdfSha256
            }
            InitiatorCiphersuite::X25519_MlKem768_ChaChaPoly_HkdfSha256(_) => {
                CiphersuiteName::X25519Mlkem768ChachaPolyHkdfSha256
            }
            #[cfg(feature = "classic-mceliece")]
            InitiatorCiphersuite::X25519_ClassicMcEliece_ChaChaPoly_HkdfSha256(_) => {
                CiphersuiteName::X25519ClassicMcElieceChachaPolyHkdfSha256
            }
            #[cfg(not(feature = "classic-mceliece"))]
            InitiatorCiphersuite::X25519_ClassicMcEliece_ChaChaPoly_HkdfSha256(_) => {
                panic!("unsupported ciphersuite")
            }
        }
    }

    fn own_ecdh_decapsulation_key(&self) -> &DHPrivateKey {
        match self {
            InitiatorCiphersuite::X25519_ChaChaPoly_HkdfSha256(
                initiator_x25519_chacha_poly_hkdf_sha256,
            ) => {
                &initiator_x25519_chacha_poly_hkdf_sha256
                    .longterm_ecdh_keys
                    .sk
            }
            InitiatorCiphersuite::X25519_MlKem768_ChaChaPoly_HkdfSha256(
                initiator_x25519_mlkem768_chacha_poly_hkdf_sha256,
            ) => {
                &initiator_x25519_mlkem768_chacha_poly_hkdf_sha256
                    .longterm_ecdh_keys
                    .sk
            }
            #[cfg(feature = "classic-mceliece")]
            InitiatorCiphersuite::X25519_ClassicMcEliece_ChaChaPoly_HkdfSha256(
                initiator_x25519_classic_mc_eliece_chacha_poly_hkdf_sha256,
            ) => {
                &initiator_x25519_classic_mc_eliece_chacha_poly_hkdf_sha256
                    .longterm_ecdh_keys
                    .sk
            }
            #[cfg(not(feature = "classic-mceliece"))]
            InitiatorCiphersuite::X25519_ClassicMcEliece_ChaChaPoly_HkdfSha256(_) => {
                panic!("unsupported ciphersuite")
            }
        }
    }

    fn own_ecdh_encapsulation_key(&self) -> &DHPublicKey {
        match self {
            InitiatorCiphersuite::X25519_ChaChaPoly_HkdfSha256(
                initiator_x25519_chacha_poly_hkdf_sha256,
            ) => {
                &initiator_x25519_chacha_poly_hkdf_sha256
                    .longterm_ecdh_keys
                    .pk
            }
            InitiatorCiphersuite::X25519_MlKem768_ChaChaPoly_HkdfSha256(
                initiator_x25519_mlkem768_chacha_poly_hkdf_sha256,
            ) => {
                &initiator_x25519_mlkem768_chacha_poly_hkdf_sha256
                    .longterm_ecdh_keys
                    .pk
            }
            #[cfg(feature = "classic-mceliece")]
            InitiatorCiphersuite::X25519_ClassicMcEliece_ChaChaPoly_HkdfSha256(
                initiator_x25519_classic_mc_eliece_chacha_poly_hkdf_sha256,
            ) => {
                &initiator_x25519_classic_mc_eliece_chacha_poly_hkdf_sha256
                    .longterm_ecdh_keys
                    .pk
            }
            #[cfg(not(feature = "classic-mceliece"))]
            InitiatorCiphersuite::X25519_ClassicMcEliece_ChaChaPoly_HkdfSha256(_) => {
                panic!("unsupported ciphersuite")
            }
        }
    }
}

impl<'a> InitiatorCiphersuiteTrait for InitiatorCiphersuite<'a> {
    fn peer_pq_encapsulation_key(&self) -> Option<<Self as CiphersuiteBase>::EncapsulationKeyRef> {
        match self {
            InitiatorCiphersuite::X25519_ChaChaPoly_HkdfSha256(_) => None,
            InitiatorCiphersuite::X25519_MlKem768_ChaChaPoly_HkdfSha256(
                initiator_x25519_mlkem768_chacha_poly_hkdf_sha256,
            ) => Some(DynamicEncapsulationKeyRef::MlKem(
                initiator_x25519_mlkem768_chacha_poly_hkdf_sha256.peer_longterm_mlkem_pk,
            )),
            #[cfg(feature = "classic-mceliece")]
            InitiatorCiphersuite::X25519_ClassicMcEliece_ChaChaPoly_HkdfSha256(
                initiator_x25519_classic_mc_eliece_chacha_poly_hkdf_sha256,
            ) => Some(DynamicEncapsulationKeyRef::CMC(
                initiator_x25519_classic_mc_eliece_chacha_poly_hkdf_sha256.peer_longterm_cmc_pk,
            )),
            #[cfg(not(feature = "classic-mceliece"))]
            InitiatorCiphersuite::X25519_ClassicMcEliece_ChaChaPoly_HkdfSha256(_) => {
                panic!("unsupported ciphersuite")
            }
        }
    }

    fn peer_ecdh_encapsulation_key(&self) -> &DHPublicKey {
        match self {
            InitiatorCiphersuite::X25519_ChaChaPoly_HkdfSha256(
                initiator_x25519_chacha_poly_hkdf_sha256,
            ) => &initiator_x25519_chacha_poly_hkdf_sha256.peer_longterm_ecdh_pk,
            InitiatorCiphersuite::X25519_MlKem768_ChaChaPoly_HkdfSha256(
                initiator_x25519_mlkem768_chacha_poly_hkdf_sha256,
            ) => &initiator_x25519_mlkem768_chacha_poly_hkdf_sha256.peer_longterm_ecdh_pk,
            #[cfg(feature = "classic-mceliece")]
            InitiatorCiphersuite::X25519_ClassicMcEliece_ChaChaPoly_HkdfSha256(
                initiator_x25519_classic_mc_eliece_chacha_poly_hkdf_sha256,
            ) => &initiator_x25519_classic_mc_eliece_chacha_poly_hkdf_sha256.peer_longterm_ecdh_pk,
            #[cfg(not(feature = "classic-mceliece"))]
            InitiatorCiphersuite::X25519_ClassicMcEliece_ChaChaPoly_HkdfSha256(_) => {
                panic!("unsupported ciphersuite")
            }
        }
    }

    fn is_pq(&self) -> bool {
        match self {
            InitiatorCiphersuite::X25519_ChaChaPoly_HkdfSha256(_) => false,
            InitiatorCiphersuite::X25519_MlKem768_ChaChaPoly_HkdfSha256(_) => true,
            #[cfg(feature = "classic-mceliece")]
            InitiatorCiphersuite::X25519_ClassicMcEliece_ChaChaPoly_HkdfSha256(_) => true,
            #[cfg(not(feature = "classic-mceliece"))]
            InitiatorCiphersuite::X25519_ClassicMcEliece_ChaChaPoly_HkdfSha256(_) => {
                panic!("unsupported ciphersuite")
            }
        }
    }

    fn pq_encapsulate(
        &self,
        rng: &mut impl CryptoRng,
    ) -> Result<
        (
            Option<<Self as CiphersuiteBase>::Ciphertext>,
            Option<<Self as CiphersuiteBase>::SharedSecret>,
        ),
        HandshakeError,
    > {
        match self {
            InitiatorCiphersuite::X25519_ChaChaPoly_HkdfSha256(_) => Ok((None, None)),
            InitiatorCiphersuite::X25519_MlKem768_ChaChaPoly_HkdfSha256(
                initiator_x25519_mlkem768_chacha_poly_hkdf_sha256,
            ) => {
                let mut rand = [0u8; libcrux_ml_kem::ENCAPS_SEED_SIZE];
                rng.fill_bytes(&mut rand);
                let (ct, ss) = libcrux_ml_kem::mlkem768::encapsulate(
                    initiator_x25519_mlkem768_chacha_poly_hkdf_sha256.peer_longterm_mlkem_pk,
                    rand,
                );

                Ok((
                    Some(DynamicCiphertext::MlKem(ct)),
                    Some(DynamicSharedSecret::MlKem(ss)),
                ))
            }
            #[cfg(feature = "classic-mceliece")]
            InitiatorCiphersuite::X25519_ClassicMcEliece_ChaChaPoly_HkdfSha256(
                initiator_x25519_classic_mc_eliece_chacha_poly_hkdf_sha256,
            ) => {
                use crate::classic_mceliece::ClassicMcEliece;
                use libcrux_traits::kem::KEM;

                let (ss, ct) = <ClassicMcEliece as KEM>::encapsulate(
                    &initiator_x25519_classic_mc_eliece_chacha_poly_hkdf_sha256
                        .peer_longterm_cmc_pk,
                    rng,
                )
                .map_err(|_| HandshakeError::CryptoError)?;

                Ok((
                    Some(DynamicCiphertext::CMC(ct)),
                    Some(DynamicSharedSecret::CMC(ss)),
                ))
            }

            #[cfg(not(feature = "classic-mceliece"))]
            InitiatorCiphersuite::X25519_ClassicMcEliece_ChaChaPoly_HkdfSha256(_) => {
                panic!("unsupported ciphersuite")
            }
        }
    }
}

impl<'a> CiphersuiteBuilder<'a> {
    pub fn new() -> Self {
        Self {
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

    pub fn longterm_ecdh_keys(mut self, keypair: &'a DHKeyPair) -> Self {
        self.longterm_ecdh_keys = Some(keypair);
        self
    }

    pub fn longterm_mlkem_encapsulation_key(
        mut self,
        encapsulation_key: &'a MlKem768PublicKey,
    ) -> Self {
        self.longterm_mlkem_encapsulation_key = Some(encapsulation_key);
        self
    }

    pub fn longterm_mlkem_decapsulation_key(
        mut self,
        decapsulation_key: &'a MlKem768PrivateKey,
    ) -> Self {
        self.longterm_mlkem_decapsulation_key = Some(decapsulation_key);
        self
    }

    pub fn peer_longterm_ecdh_pk(mut self, ecdh_pk: &'a DHPublicKey) -> Self {
        self.peer_longterm_ecdh_pk = Some(ecdh_pk);
        self
    }

    pub fn peer_longterm_mlkem_pk(mut self, encapsulation_key: &'a MlKem768PublicKey) -> Self {
        self.peer_longterm_mlkem_pk = Some(encapsulation_key);
        self
    }

    #[cfg(feature = "classic-mceliece")]
    pub fn longterm_cmc_encapsulation_key(mut self, encapsulation_key: &'a PublicKey) -> Self {
        self.longterm_cmc_encapsulation_key = Some(encapsulation_key);
        self
    }

    #[cfg(feature = "classic-mceliece")]
    pub fn longterm_cmc_decapsulation_key(mut self, decapsulation_key: &'a SecretKey) -> Self {
        self.longterm_cmc_decapsulation_key = Some(decapsulation_key);
        self
    }

    #[cfg(feature = "classic-mceliece")]
    pub fn peer_longterm_cmc_pk(mut self, encapsulation_key: &'a PublicKey) -> Self {
        self.peer_longterm_cmc_pk = Some(encapsulation_key);
        self
    }

    pub fn finish_initiator(
        self,
        name: CiphersuiteName,
    ) -> Result<InitiatorCiphersuite<'a>, HandshakeError> {
        let (peer_longterm_ecdh_pk, longterm_ecdh_keys) = self.check_common_keys_initiator()?;
        match name {
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
                    return Err(HandshakeError::BuilderState);
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
                let Some(peer_longterm_cmc_pk) = self.peer_longterm_cmc_pk else {
                    return Err(HandshakeError::BuilderState);
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
                panic!("unsupported cipersuite")
            }
        }
    }

    pub fn finish_responder(
        self,
        name: CiphersuiteName,
    ) -> Result<ResponderCiphersuite<'a>, HandshakeError> {
        let Some(longterm_ecdh_keys) = self.longterm_ecdh_keys else {
            return Err(HandshakeError::BuilderState);
        };

        match name {
            CiphersuiteName::X25519ChachaPolyHkdfSha256 => {
                Ok(ResponderCiphersuite::X25519_ChaChaPoly_HkdfSha256(
                    ResponderX25519ChaChaPolyHkdfSha256 { longterm_ecdh_keys },
                ))
            }
            CiphersuiteName::X25519Mlkem768ChachaPolyHkdfSha256 => {
                let Some(longterm_pq_encapsulation_key) = self.longterm_mlkem_encapsulation_key
                else {
                    return Err(HandshakeError::BuilderState);
                };
                let Some(longterm_pq_decapsulation_key) = self.longterm_mlkem_decapsulation_key
                else {
                    return Err(HandshakeError::BuilderState);
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
                let Some(longterm_pq_encapsulation_key) = self.longterm_cmc_encapsulation_key
                else {
                    return Err(HandshakeError::BuilderState);
                };
                let Some(longterm_pq_decapsulation_key) = self.longterm_cmc_decapsulation_key
                else {
                    return Err(HandshakeError::BuilderState);
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
                panic!("Unsupported ciphersuite")
            }
        }
    }

    fn check_common_keys_initiator(
        &self,
    ) -> Result<(&'a DHPublicKey, &'a DHKeyPair), HandshakeError> {
        let Some(peer_longterm_ecdh_pk) = self.peer_longterm_ecdh_pk else {
            return Err(HandshakeError::BuilderState);
        };
        let Some(longterm_ecdh_keys) = self.longterm_ecdh_keys else {
            return Err(HandshakeError::BuilderState);
        };
        Ok((peer_longterm_ecdh_pk, longterm_ecdh_keys))
    }
}

pub trait InitiatorCiphersuiteTrait: CiphersuiteBase {
    fn is_pq(&self) -> bool;
    fn peer_pq_encapsulation_key(&self) -> Option<<Self as CiphersuiteBase>::EncapsulationKeyRef>;

    fn peer_ecdh_encapsulation_key(&self) -> &DHPublicKey;

    fn pq_encapsulate(
        &self,
        rng: &mut impl CryptoRng,
    ) -> Result<
        (
            Option<<Self as CiphersuiteBase>::Ciphertext>,
            Option<<Self as CiphersuiteBase>::SharedSecret>,
        ),
        HandshakeError,
    >;
}
pub trait ResponderCiphersuiteTrait: CiphersuiteBase {
    type DecapsulationKey;
    fn own_pq_encapsulation_key(&self) -> Option<<Self as CiphersuiteBase>::EncapsulationKeyRef>;

    fn pq_decapsulate(
        &self,
        ciphertext: Option<&<Self as CiphersuiteBase>::Ciphertext>,
    ) -> Result<Option<<Self as CiphersuiteBase>::SharedSecret>, HandshakeError>;
}

pub struct ResponderX25519ChaChaPolyHkdfSha256<'a> {
    pub longterm_ecdh_keys: &'a DHKeyPair,
}

pub struct ResponderX25519MlKem768ChaChaPolyHkdfSha256<'a> {
    pub longterm_ecdh_keys: &'a DHKeyPair,
    pub longterm_pq_encapsulation_key: &'a MlKem768PublicKey,
    pub longterm_pq_decapsulation_key: &'a MlKem768PrivateKey,
}
pub struct InitiatorX25519Mlkem768ChachaPolyHkdfSha256<'a> {
    pub longterm_ecdh_keys: &'a DHKeyPair,
    pub peer_longterm_ecdh_pk: &'a DHPublicKey,
    pub peer_longterm_mlkem_pk: &'a libcrux_ml_kem::mlkem768::MlKem768PublicKey,
}
pub struct InitiatorX25519ChachaPolyHkdfSha256<'a> {
    pub longterm_ecdh_keys: &'a DHKeyPair,
    pub peer_longterm_ecdh_pk: &'a DHPublicKey,
}

#[cfg(feature = "classic-mceliece")]
pub struct InitiatorX25519ClassicMcElieceChachaPolyHkdfSha256<'a> {
    pub longterm_ecdh_keys: &'a DHKeyPair,
    pub peer_longterm_ecdh_pk: &'a DHPublicKey,
    pub peer_longterm_cmc_pk: &'a PublicKey,
}
#[cfg(not(feature = "classic-mceliece"))]
pub struct InitiatorX25519ClassicMcElieceChachaPolyHkdfSha256 {}
#[cfg(feature = "classic-mceliece")]
pub struct ResponderX25519ClassicMcElieceChaChaPolyHkdfSha256<'a> {
    pub longterm_ecdh_keys: &'a DHKeyPair,
    pub longterm_pq_encapsulation_key: &'a PublicKey,
    pub longterm_pq_decapsulation_key: &'a SecretKey,
}

impl<'a> ResponderCiphersuiteTrait for ResponderCiphersuite<'a> {
    type DecapsulationKey = DynamicDecapsulationKey;

    fn own_pq_encapsulation_key(&self) -> Option<<Self as CiphersuiteBase>::EncapsulationKeyRef> {
        match self {
            ResponderCiphersuite::X25519_MlKem768_ChaChaPoly_HkdfSha256(
                responder_x25519_ml_kem768_cha_cha_poly_hkdf_sha256,
            ) => Some(DynamicEncapsulationKeyRef::MlKem(
                responder_x25519_ml_kem768_cha_cha_poly_hkdf_sha256.longterm_pq_encapsulation_key,
            )),
            #[cfg(feature = "classic-mceliece")]
            ResponderCiphersuite::X25519_ClassicMcEliece_ChaChaPoly_HkdfSha256(
                responder_x25519_cmc_cha_cha_poly_hkdf_sha256,
            ) => Some(DynamicEncapsulationKeyRef::CMC(
                responder_x25519_cmc_cha_cha_poly_hkdf_sha256.longterm_pq_encapsulation_key,
            )),
            #[cfg(not(feature = "classic-mceliece"))]
            ResponderCiphersuite::X25519_ClassicMcEliece_ChaChaPoly_HkdfSha256(_) => {
                panic!("unsupported ciphersuite")
            }
            ResponderCiphersuite::X25519_ChaChaPoly_HkdfSha256(_) => None,
        }
    }

    fn pq_decapsulate(
        &self,
        ciphertext: Option<&<Self as CiphersuiteBase>::Ciphertext>,
    ) -> Result<Option<<Self as CiphersuiteBase>::SharedSecret>, HandshakeError> {
        let Some(ciphertext) = ciphertext else {
            return Ok(None);
        };
        match self {
            ResponderCiphersuite::X25519_MlKem768_ChaChaPoly_HkdfSha256(
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

                Ok(Some(DynamicSharedSecret::MlKem(shared_secret)))
            }
            #[cfg(feature = "classic-mceliece")]
            ResponderCiphersuite::X25519_ClassicMcEliece_ChaChaPoly_HkdfSha256(
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
                Ok(Some(DynamicSharedSecret::CMC(shared_secret)))
            }
            #[cfg(not(feature = "classic-mceliece"))]
            ResponderCiphersuite::X25519_ClassicMcEliece_ChaChaPoly_HkdfSha256(_) => {
                panic!("unsupported ciphersuite")
            }
            ResponderCiphersuite::X25519_ChaChaPoly_HkdfSha256(_) => Ok(None),
        }
    }
}
