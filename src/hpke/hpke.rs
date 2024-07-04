#![allow(non_camel_case_types, non_snake_case, unused_imports)]

use libcrux_ecdh::{self, secret_to_public, x25519_derive, X25519PublicKey};
use libcrux_ml_kem::mlkem768;

use crate::kem::{
    self, Ct, PublicKey, Ss, X25519MlKem768Draft00PrivateKey, X25519MlKem768Draft00PublicKey,
    XWingKemDraft02PrivateKey, XWingKemDraft02PublicKey,
};

use super::aead::*;
use super::kdf::*;
use super::kem::*;

use super::errors::*;

// === Constants ===

///  A one-byte value indicating the HPKE mode, defined in the following table.
///
/// | Mode          | Value |
/// | ------------- | ----- |
/// | mode_base     | 0x00  |
/// | mode_psk      | 0x01  |
/// | mode_auth     | 0x02  |
/// | mode_auth_psk | 0x03  |
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Mode {
    /// 0x00
    mode_base,
    /// 0x01
    mode_psk,
    /// 0x02
    mode_auth,
    /// 0x03
    mode_auth_psk,
}

// === Types ===

#[derive(Clone, Copy, Debug)]
pub struct HPKEConfig(pub Mode, pub KEM, pub KDF, pub AEAD);

pub type KemOutput = Vec<u8>;
pub type Ciphertext = Vec<u8>;
pub struct HPKECiphertext(pub KemOutput, pub Ciphertext);

pub type HpkePrivateKey = [u8];
pub type HpkePublicKey = [u8];
pub struct HPKEKeyPair(pub Vec<u8>, pub Vec<u8>); // Private, Public

pub type AdditionalData = [u8];
pub type Psk = [u8];
pub type PskId = [u8];

// === String labels ===

/// "info_hash" label for [`LabeledExtract()`].
///
/// See [`KeySchedule`] for details.
fn info_hash_label() -> Vec<u8> {
    vec![
        0x69u8, 0x6eu8, 0x66u8, 0x6fu8, 0x5fu8, 0x68u8, 0x61u8, 0x73u8, 0x68u8,
    ]
}

/// "psk_id_hash" label for [`LabeledExtract()`].
///
/// See [`KeySchedule`] for details.
fn psk_id_hash_label() -> Vec<u8> {
    vec![
        0x70u8, 0x73u8, 0x6bu8, 0x5fu8, 0x69u8, 0x64u8, 0x5fu8, 0x68u8, 0x61u8, 0x73u8, 0x68u8,
    ]
}

/// "secret" label for [`LabeledExtract()`].
///
/// See [`KeySchedule`] for details.
fn secret_label() -> Vec<u8> {
    vec![0x73u8, 0x65u8, 0x63u8, 0x72u8, 0x65u8, 0x74u8]
}

/// "key" label for [`LabeledExpand()`].
///
/// See [`KeySchedule`] for details.
fn key_label() -> Vec<u8> {
    vec![0x6bu8, 0x65u8, 0x79u8]
}

/// "base_nonce" label for [`LabeledExpand()`].
///
/// See [`KeySchedule`] for details.
fn base_nonce_label() -> Vec<u8> {
    vec![
        0x62u8, 0x61u8, 0x73u8, 0x65u8, 0x5fu8, 0x6eu8, 0x6fu8, 0x6eu8, 0x63u8, 0x65u8,
    ]
}

/// "exp" label for [`LabeledExpand()`].
///
/// See [`KeySchedule`] for details.
fn exp_label() -> Vec<u8> {
    vec![0x65u8, 0x78u8, 0x70u8]
}

/// "sec" label for [`LabeledExpand()`].
///
/// See [`Context_Export`] for details.
fn sec_label() -> Vec<u8> {
    vec![0x73u8, 0x65u8, 0x63u8]
}

/// Get the numeric value of the `mode`.
///
/// See [`Mode`] for details.
fn hpke_mode_label(mode: Mode) -> Vec<u8> {
    match mode {
        Mode::mode_base => vec![0x00u8],
        Mode::mode_psk => vec![0x01u8],
        Mode::mode_auth => vec![0x02u8],
        Mode::mode_auth_psk => vec![0x03u8],
    }
}

/// Get the numeric value of the `aead_id`.
///
/// See [`AEAD`] for details.
fn hpke_aead_value(aead_id: AEAD) -> u16 {
    match aead_id {
        AEAD::AES_128_GCM => 0x0001u16,
        AEAD::AES_256_GCM => 0x0002u16,
        AEAD::ChaCha20Poly1305 => 0x0003u16,
        AEAD::Export_only => 0xFFFFu16,
    }
}

/// Get the KEM algorithm from the config
fn kem(config: HPKEConfig) -> KEM {
    let HPKEConfig(_, kem, _, _) = config;
    kem
}

// === Context Helper ===

type EncodedHpkePublicKey = Vec<u8>;
type EncodedHpkePublicKeyIn = [u8];
type ExporterSecret = Vec<u8>;
type SequenceCounter = u32;
type Context = (Key, Nonce, SequenceCounter, ExporterSecret);
type SenderContext = (EncodedHpkePublicKey, Context);

pub type SenderContextResult = Result<SenderContext, HpkeError>;
pub type ContextResult = Result<Context, HpkeError>;
pub type EmptyResult = Result<(), HpkeError>;

/// Cipher suite identifier
///
/// See [`KeySchedule`] for more details.
///
/// The implicit `suite_id` value used within `LabeledExtract` and `LabeledExpand`
/// is defined based on them as follows:
///
/// ```text
/// suite_id = concat(
///     "HPKE",
///     I2OSP(kem_id, 2),
///     I2OSP(kdf_id, 2),
///     I2OSP(aead_id, 2)
///   )
/// ```
fn suite_id(config: HPKEConfig) -> Vec<u8> {
    let HPKEConfig(_, kem, kdf, aead) = config;
    let mut suite_id = vec![0x48u8, 0x50u8, 0x4bu8, 0x45u8]; // "HPKE"
    suite_id.extend_from_slice(&kem_value(kem).to_be_bytes());
    suite_id.extend_from_slice(&kdf_value(kdf).to_be_bytes());
    suite_id.extend_from_slice(&hpke_aead_value(aead).to_be_bytes());
    suite_id
}

/// The default PSK ""
///
/// ```text
/// default_psk = ""
/// ```
///
/// See [`KeySchedule`] for more details.
fn default_psk() -> Vec<u8> {
    Vec::new()
}

/// The default PSK ID ""
///
/// ```text
/// default_psk_id = ""
/// ```
///
/// See [`KeySchedule`] for more details.
fn default_psk_id() -> Vec<u8> {
    Vec::new()
}

fn empty_bytes() -> Vec<u8> {
    Vec::new()
}

/// Creating the Encryption Context
///
/// ...
///
/// ```text
/// def VerifyPSKInputs(mode, psk, psk_id):
///   got_psk = (psk != default_psk)
///   got_psk_id = (psk_id != default_psk_id)
///   if got_psk != got_psk_id:
///     raise Exception("Inconsistent PSK inputs")
///
///   if got_psk and (mode in [mode_base, mode_auth]):
///     raise Exception("PSK input provided when not needed")
///   if (not got_psk) and (mode in [mode_psk, mode_auth_psk]):
///     raise Exception("Missing required PSK input")
/// ```
///
/// See [`KeySchedule`] for detail.
pub fn VerifyPSKInputs(config: HPKEConfig, psk: &Psk, psk_id: &PskId) -> EmptyResult {
    let HPKEConfig(mode, _kem, _kdf, _aead) = config;
    let got_psk = psk.len() != 0;
    let got_psk_id = psk_id.len() != 0;
    if got_psk != got_psk_id {
        EmptyResult::Err(HpkeError::InconsistentPskInputs)
    } else {
        // FIXME: https://github.com/hacspec/hacspec/issues/85
        if got_psk && (mode == Mode::mode_base || mode == Mode::mode_auth) {
            EmptyResult::Err(HpkeError::UnnecessaryPsk)
        } else {
            if !got_psk && (mode == Mode::mode_psk || mode == Mode::mode_auth_psk) {
                EmptyResult::Err(HpkeError::MissingPsk)
            } else {
                EmptyResult::Ok(())
            }
        }
    }
}

/// ## Creating the Encryption Context
///
///
/// The variants of HPKE defined in this document share a common
/// key schedule that translates the protocol inputs into an encryption
/// context. The key schedule inputs are as follows:
///
/// * `mode` - A one-byte value indicating the HPKE mode, defined in [`Mode`].
/// * `shared_secret` - A KEM shared secret generated for this transaction.
/// * `info` - Application-supplied information (optional; default value
///   "").
/// * `psk` - A pre-shared key (PSK) held by both the sender
///   and the recipient (optional; default value "").
/// * `psk_id` - An identifier for the PSK (optional; default value "").
///
/// Senders and recipients MUST validate KEM inputs and outputs as described
/// in [`KEM`].
///
/// The `psk` and `psk_id` fields MUST appear together or not at all.
/// That is, if a non-default value is provided for one of them, then
/// the other MUST be set to a non-default value. This requirement is
/// encoded in [`VerifyPSKInputs()`] below.
///
/// The `psk`, `psk_id`, and `info` fields have maximum lengths that depend
/// on the KDF itself, on the definition of [`LabeledExtract()`], and on the
/// constant labels used together with them. See [KDF Input Length](mod@crate::hpke::kdf#input-length-restrictions) for
/// precise limits on these lengths.
///
/// The `key`, `base_nonce`, and `exporter_secret` computed by the key schedule
/// have the property that they are only known to the holder of the recipient
/// private key, and the entity that used the KEM to generate `shared_secret` and
/// `enc`.
///
/// In the Auth and AuthPSK modes, the recipient is assured that the sender
/// held the private key `skS`. This assurance is limited for the DHKEM
/// variants defined in this document because of key-compromise impersonation,
/// as described in [`mod@crate::hpke::kem#dh-based-kem`] and the [security properties section](crate#security-properties). If in the PSK and
/// AuthPSK modes, the `psk` and `psk_id` arguments are provided as required,
/// then the recipient is assured that the sender held the corresponding
/// pre-shared key. See the security properties section on the [module page](`crate`) for more details.
///
/// The HPKE algorithm identifiers, i.e., the KEM `kem_id`, KDF `kdf_id`, and
/// AEAD `aead_id` 2-byte code points as defined in [`KEM`], [`KDF`],
/// and [`AEAD`], respectively, are assumed implicit from the implementation
/// and not passed as parameters.
/// ```text
/// def KeySchedule<ROLE>(mode, shared_secret, info, psk, psk_id):
///   VerifyPSKInputs(mode, psk, psk_id)
///
///   psk_id_hash = LabeledExtract("", "psk_id_hash", psk_id)
///   info_hash = LabeledExtract("", "info_hash", info)
///   key_schedule_context = concat(mode, psk_id_hash, info_hash)
///
///   secret = LabeledExtract(shared_secret, "secret", psk)
///
///   key = LabeledExpand(secret, "key", key_schedule_context, Nk)
///   base_nonce = LabeledExpand(secret, "base_nonce",
///                              key_schedule_context, Nn)
///   exporter_secret = LabeledExpand(secret, "exp",
///                                   key_schedule_context, Nh)
///
///   return Context<ROLE>(key, base_nonce, 0, exporter_secret)
/// ```
///
/// The `ROLE` template parameter is either S or R, depending on the role of
/// sender or recipient, respectively. See [HPKE DEM](`ContextS_Seal`) for a discussion of the
/// key schedule output, including the role-specific `Context` structure and its API.
///
/// Note that the `key_schedule_context` construction in [`KeySchedule()`] is
/// equivalent to serializing a structure of the following form in the TLS presentation
/// syntax:
///
/// ~~~text
/// struct {
///     uint8 mode;
///     opaque psk_id_hash[Nh];
///     opaque info_hash[Nh];
/// } KeyScheduleContext;
/// ~~~
///
/// This function takes the `<MODE>` as argument in [`HPKEConfig`].
pub fn KeySchedule(
    config: HPKEConfig,
    shared_secret: &SharedSecret,
    info: &Info,
    psk: &Psk,
    psk_id: &PskId,
) -> ContextResult {
    VerifyPSKInputs(config, &psk, psk_id)?;
    let HPKEConfig(mode, _kem, kdf, aead) = config;

    let psk_id_hash = LabeledExtract(
        kdf,
        suite_id(config),
        &empty_bytes(),
        psk_id_hash_label(),
        psk_id,
    )?;
    let info_hash = LabeledExtract(
        kdf,
        suite_id(config),
        &empty_bytes(),
        info_hash_label(),
        info,
    )?;
    let mut key_schedule_context = hpke_mode_label(mode);
    key_schedule_context.extend_from_slice(&psk_id_hash);
    key_schedule_context.extend_from_slice(&info_hash);

    let secret = LabeledExtract(kdf, suite_id(config), shared_secret, secret_label(), psk)?;

    let key = LabeledExpand(
        kdf,
        suite_id(config),
        &secret,
        key_label(),
        &key_schedule_context,
        Nk(aead),
    )?;
    let base_nonce = LabeledExpand(
        kdf,
        suite_id(config),
        &secret,
        base_nonce_label(),
        &key_schedule_context,
        Nn(aead),
    )?;
    let exporter_secret = LabeledExpand(
        kdf,
        suite_id(config),
        &secret,
        exp_label(),
        &key_schedule_context,
        Nh(kdf),
    )?;

    Ok((key, base_nonce, 0u32, exporter_secret))
}

/// ## Encryption to a Public Key - Sender
///
/// The most basic function of an HPKE scheme is to enable encryption to the
/// holder of a given KEM private key. The [`SetupBaseS()`] and [`SetupBaseR()`]
/// procedures establish contexts that can be used to encrypt and decrypt,
/// respectively, for a given private key. The KEM shared secret is combined via
/// the KDF with information describing the key exchange, as well as the explicit
/// info parameter provided by the caller.The parameter pkR is a public key,
/// and enc is an encapsulated KEM shared secret.
///
/// ```text
/// def SetupBaseS(pkR, info):
///   shared_secret, enc = Encap(pkR)
///   return enc, KeyScheduleS(mode_base, shared_secret, info,
///                            default_psk, default_psk_id)
/// ```
pub fn SetupBaseS(
    config: HPKEConfig,
    pkR: &HpkePublicKey,
    info: &Info,
    randomness: Randomness,
) -> SenderContextResult {
    let (shared_secret, enc) = match config.1 {
        KEM::DHKEM_P256_HKDF_SHA256
        | KEM::DHKEM_P384_HKDF_SHA384
        | KEM::DHKEM_P521_HKDF_SHA512
        | KEM::DHKEM_X25519_HKDF_SHA256
        | KEM::DHKEM_X448_HKDF_SHA512 => Encap(kem(config), pkR, randomness)?,
        KEM::X25519Kyber768Draft00 => {
            // FIXME: clean up
            // Decode the public key
            let X25519MlKem768Draft00PublicKey {
                mlkem: kyber,
                x25519,
            } = X25519MlKem768Draft00PublicKey::decode(pkR).unwrap();
            let (ss1, enc1) = Encap(
                KEM::DHKEM_X25519_HKDF_SHA256,
                &x25519.0,
                randomness[0..32].to_vec(),
            )?;
            let (ss2, enc2) = Kyber768Draft00_Encap(kyber.as_ref(), randomness[32..64].to_vec())?;
            let ct = crate::kem::Ct::X25519MlKem768Draft00(
                enc2.as_slice().try_into().unwrap(),
                libcrux_ecdh::X25519PublicKey(enc1.try_into().unwrap()),
            );
            let ss = crate::kem::Ss::X25519MlKem768Draft00(
                ss2.as_slice().try_into().unwrap(),
                libcrux_ecdh::X25519PublicKey(ss1.try_into().unwrap()),
            );
            (ss.encode(), ct.encode())
        }
        KEM::XWingDraft02 => {
            // TODO: This should re-use PublicKey::encapsulate but we need
            // CryptoRng + Rng for that, not just a slice of randomness
            let XWingKemDraft02PublicKey { pk_m, pk_x } =
                XWingKemDraft02PublicKey::decode(pkR).map_err(|_| HpkeError::EncapError)?;

            let (ct_m, ss_m) = mlkem768::encapsulate(
                &pk_m,
                randomness[0..32]
                    .try_into()
                    .map_err(|_| HpkeError::EncapError)?,
            );
            let ek_x = libcrux_ecdh::X25519PrivateKey(
                randomness[..32]
                    .try_into()
                    .map_err(|_| HpkeError::EncapError)?,
            );
            let ct_x: [u8; 32] = secret_to_public(libcrux_ecdh::Algorithm::X25519, &ek_x)
                .map_err(|_| HpkeError::EncapError)?
                .try_into()
                .expect("should have received the right number of bytes on success");
            let ct_x = X25519PublicKey(ct_x);

            let ss_x = x25519_derive(&pk_x, &ek_x).map_err(|_| HpkeError::EncapError)?;

            let ct = Ct::XWingKemDraft02(
                ct_m.as_slice()
                    .try_into()
                    .map_err(|_| HpkeError::EncapError)?,
                ct_x.0
                    .as_slice()
                    .try_into()
                    .map_err(|_| HpkeError::EncapError)?,
            );
            let ss = Ss::XWingKemDraft02(
                ss_m.as_slice()
                    .try_into()
                    .map_err(|_| HpkeError::EncapError)?,
                ss_x.0
                    .as_slice()
                    .try_into()
                    .map_err(|_| HpkeError::EncapError)?,
                ct_x,
                pk_x,
            );
            (ss.encode(), ct.encode())
        }
    };

    let key_schedule = KeySchedule(
        config,
        &shared_secret,
        info,
        &default_psk(),
        &default_psk_id(),
    )?;
    Ok((enc, key_schedule))
}

/// ## Encryption to a Public Key - Receiver
///
/// See [`SetupBaseS`] for more details.
///
/// ```text
/// def SetupBaseR(enc, skR, info):
///   shared_secret = Decap(enc, skR)
///   return KeyScheduleR(mode_base, shared_secret, info,
///                       default_psk, default_psk_id)
/// ```
pub fn SetupBaseR(
    config: HPKEConfig,
    enc: &EncodedHpkePublicKeyIn,
    skR: &HpkePrivateKey,
    info: &Info,
) -> ContextResult {
    let shared_secret = match config.1 {
        KEM::DHKEM_P256_HKDF_SHA256
        | KEM::DHKEM_P384_HKDF_SHA384
        | KEM::DHKEM_P521_HKDF_SHA512
        | KEM::DHKEM_X25519_HKDF_SHA256
        | KEM::DHKEM_X448_HKDF_SHA512 => Decap(kem(config), enc, skR)?,
        KEM::X25519Kyber768Draft00 => {
            // FIXME: clean up
            // Decode the public key
            let X25519MlKem768Draft00PrivateKey {
                mlkem: kyber,
                x25519,
            } = X25519MlKem768Draft00PrivateKey::decode(skR).unwrap();
            let ss1 = Decap(KEM::DHKEM_X25519_HKDF_SHA256, &enc[0..32], &x25519.0)?;
            let ss2 = Kyber768Draft00_Decap(kyber.as_ref(), &enc[32..])?;
            let ss = crate::kem::Ss::X25519MlKem768Draft00(
                ss2.as_slice().try_into().unwrap(),
                libcrux_ecdh::X25519PublicKey(ss1.try_into().unwrap()),
            );
            ss.encode()
        }
        KEM::XWingDraft02 => {
            let ct = kem::Ct::decode(crate::kem::Algorithm::XWingKemDraft02, enc)
                .map_err(|_| HpkeError::DecapError)?;
            let sk = crate::kem::XWingKemDraft02PrivateKey::decode(skR)
                .map_err(|_| HpkeError::DecapError)?;
            let sk = &kem::PrivateKey::XWingKemDraft02(sk);
            let ss = ct.decapsulate(sk).map_err(|_| HpkeError::DecapError)?;

            ss.encode()
        }
    };
    let key_schedule = KeySchedule(
        config,
        &shared_secret,
        info,
        &default_psk(),
        &default_psk_id(),
    )?;
    Ok(key_schedule)
}

/// ## Authentication using a Pre-Shared Key - Sender
///
/// This variant extends the base mechanism by allowing the recipient to
/// authenticate that the sender possessed a given PSK. The PSK also improves
/// confidentiality guarantees in certain adversary models, as described in the
/// [security properties](crate#security-properties). We assume that both parties have been provisioned with
/// both the PSK value psk and another byte string `psk_id` that is used to identify
/// which PSK should be used.
/// The primary difference from the base case is that the psk and psk_id values
/// are used as `ikm` inputs to the KDF (instead of using the empty string). The
/// PSK MUST have at least 32 bytes of entropy and SHOULD be of length Nh bytes
/// or longer. See the [PSK Recommendations](crate#pre-shared-key-recommendations) for a more detailed discussion.
///
/// ```text
/// def SetupPSKS(pkR, info, psk, psk_id):
///   shared_secret, enc = Encap(pkR)
///   return enc, KeyScheduleS(mode_psk, shared_secret, info, psk, psk_id)
/// ```
pub fn SetupPSKS(
    config: HPKEConfig,
    pkR: &HpkePublicKey,
    info: &Info,
    psk: &Psk,
    psk_id: &PskId,
    randomness: Randomness,
) -> SenderContextResult {
    let (shared_secret, enc) = Encap(kem(config), pkR, randomness)?;
    let key_schedule = KeySchedule(config, &shared_secret, info, psk, psk_id)?;
    Ok((enc, key_schedule))
}

/// ## Authentication using a Pre-Shared Key - Receiver
///
/// See [`SetupPSKS`] for more details.
///
/// ```text
/// def SetupPSKR(enc, skR, info, psk, psk_id):
///   shared_secret = Decap(enc, skR)
///   return KeyScheduleR(mode_psk, shared_secret, info, psk, psk_id)
/// ```
pub fn SetupPSKR(
    config: HPKEConfig,
    enc: &EncodedHpkePublicKeyIn,
    skR: &HpkePrivateKey,
    info: &Info,
    psk: &Psk,
    psk_id: &PskId,
) -> ContextResult {
    let shared_secret = Decap(kem(config), enc, skR)?;
    let key_schedule = KeySchedule(config, &shared_secret, info, psk, psk_id)?;
    Ok(key_schedule)
}

/// ## Authentication using an Asymmetric Key - Sender
///
/// This variant extends the base mechanism by allowing the recipient
/// to authenticate that the sender possessed a given KEM private key.
/// This is because [`AuthDecap(enc, skR, pkS)`](`crate::hpke::kem::AuthDecap()`) produces the correct KEM
/// shared secret only if the encapsulated value `enc` was produced by
/// [`AuthEncap(pkR, skS)`](`crate::hpke::kem::AuthEncap()`), where `skS` is the private key corresponding
/// to `pkS`.  In other words, at most two entities (precisely two, in the case
/// of DHKEM) could have produced this secret, so if the recipient is at most one, then
/// the sender is the other with overwhelming probability.
///
/// The primary difference from the base case is that the calls to
/// `Encap()` and `Decap()` are replaced with calls to [`AuthEncap()`](`crate::hpke::kem::AuthEncap()`) and
/// [`AuthDecap()`](`crate::hpke::kem::AuthDecap()`), which add the sender public key to their internal
/// context string. The function parameters `pkR` and `pkS` are
/// public keys, and `enc` is an encapsulated KEM shared secret.
///
/// Obviously, this variant can only be used with a KEM that provides
/// [`AuthEncap()`](`crate::hpke::kem::AuthEncap()`) and [`AuthDecap()`](`crate::hpke::kem::AuthDecap()`) procedures.
///
/// This mechanism authenticates only the key pair of the sender, not
/// any other identifier.  If an application wishes to bind HPKE
/// ciphertexts or exported secrets to another identity for the sender
/// (e.g., an email address or domain name), then this identifier should be
/// included in the `info` parameter to avoid identity mis-binding issues [IMB].
///
/// ```text
/// def SetupAuthS(pkR, info, skS):
///   shared_secret, enc = AuthEncap(pkR, skS)
///   return enc, KeyScheduleS(mode_auth, shared_secret, info,
///                            default_psk, default_psk_id)
/// ```
///
/// [IMB]: https://doi.org/10.1007/bf00124891
pub fn SetupAuthS(
    config: HPKEConfig,
    pkR: &HpkePublicKey,
    info: &Info,
    skS: &PrivateKeyIn,
    randomness: Randomness,
) -> SenderContextResult {
    let (shared_secret, enc) = AuthEncap(kem(config), pkR, skS, randomness)?;
    let key_schedule = KeySchedule(
        config,
        &shared_secret,
        info,
        &default_psk(),
        &default_psk_id(),
    )?;
    Ok((enc, key_schedule))
}

/// ## Authentication using an Asymmetric Key - Receiver
///
/// See [`SetupAuthS`] for more details.
///
/// ```text
/// def SetupAuthR(enc, skR, info, pkS):
///   shared_secret = AuthDecap(enc, skR, pkS)
///   return KeyScheduleR(mode_auth, shared_secret, info,
///                       default_psk, default_psk_id)
/// ```
pub fn SetupAuthR(
    config: HPKEConfig,
    enc: &EncodedHpkePublicKeyIn,
    skR: &HpkePrivateKey,
    info: &Info,
    pkS: &PublicKeyIn,
) -> ContextResult {
    let shared_secret = AuthDecap(kem(config), enc, skR, pkS)?;
    let key_schedule = KeySchedule(
        config,
        &shared_secret,
        info,
        &default_psk(),
        &default_psk_id(),
    )?;
    Ok(key_schedule)
}

/// ## Authentication using both a PSK and an Asymmetric Key - Sender
///
/// This mode is a straightforward combination of the PSK and
/// authenticated modes.  The PSK is passed through to the key schedule
/// as in the former, and as in the latter, we use the authenticated KEM
/// variants.
///
/// ```text
/// def SetupAuthPSKS(pkR, info, psk, psk_id, skS):
///   shared_secret, enc = AuthEncap(pkR, skS)
///   return enc, KeyScheduleS(mode_auth_psk, shared_secret, info,
///                            psk, psk_id)
/// ```
///
/// The PSK MUST have at least 32 bytes of entropy and SHOULD be of length `Nh`
/// bytes or longer.
pub fn SetupAuthPSKS(
    config: HPKEConfig,
    pkR: &HpkePublicKey,
    info: &Info,
    psk: &Psk,
    psk_id: &PskId,
    skS: &HpkePrivateKey,
    randomness: Randomness,
) -> SenderContextResult {
    let (shared_secret, enc) = AuthEncap(kem(config), pkR, skS, randomness)?;
    let key_schedule = KeySchedule(config, &shared_secret, info, psk, psk_id)?;
    Ok((enc, key_schedule))
}

/// ## Authentication using both a PSK and an Asymmetric Key - Receiver
///
/// See [`SetupAuthPSKS`] for more details.
///
/// ```text
/// def SetupAuthPSKR(enc, skR, info, psk, psk_id, pkS):
///   shared_secret = AuthDecap(enc, skR, pkS)
///   return KeyScheduleR(mode_auth_psk, shared_sec
/// ```
pub fn SetupAuthPSKR(
    config: HPKEConfig,
    enc: &EncodedHpkePublicKeyIn,
    skR: &HpkePrivateKey,
    info: &Info,
    psk: &Psk,
    psk_id: &PskId,
    pkS: &PublicKeyIn,
) -> ContextResult {
    let shared_secret = AuthDecap(kem(config), enc, skR, pkS)?;
    let key_schedule = KeySchedule(config, &shared_secret, info, psk, psk_id)?;
    Ok(key_schedule)
}

// === Stateful API ===

fn bitxor(mut lhs: Vec<u8>, rhs: Vec<u8>) -> Vec<u8> {
    assert_eq!(lhs.len(), rhs.len());
    for i in 0..lhs.len() {
        lhs[i] = lhs[i] ^ rhs[i]
    }
    lhs
}

/// ### Compute Nonce
///
/// The sequence number provides nonce uniqueness: The nonce used for
/// each encryption or decryption operation is the result of XORing
/// `base_nonce` with the current sequence number, encoded as a big-endian
/// integer of the same length as `base_nonce`. Implementations MAY use a
/// sequence number that is shorter than the nonce length (padding on the left
/// with zero), but MUST raise an error if the sequence number overflows.
///
/// ```text
/// def Context<ROLE>.ComputeNonce(seq):
///   seq_bytes = I2OSP(seq, Nn)
///   return xor(self.base_nonce, seq_bytes)
/// ```
pub fn ComputeNonce(aead_id: AEAD, base_nonce: &Nonce, seq: SequenceCounter) -> Vec<u8> {
    let seq = seq.to_be_bytes();
    let Nn = Nn(aead_id);
    let mut seq_bytes = vec![0u8; Nn - 4];
    seq_bytes.extend_from_slice(&seq);
    bitxor(base_nonce.clone(), seq_bytes)
}

/// ## Encryption and Decryption
///
/// HPKE allows multiple encryption operations to be done based on a
/// given setup transaction.  Since the public-key operations involved
/// in setup are typically more expensive than symmetric encryption or
/// decryption, this allows applications to amortize the cost of the
/// public-key operations, reducing the overall overhead.
///
/// In order to avoid nonce reuse, however, this encryption must be
/// stateful. Each of the setup procedures above produces a role-specific
/// context object that stores the AEAD and Secret Export parameters.
/// The AEAD parameters consist of:
///
/// * The AEAD algorithm in use
/// * A secret `key`
/// * A base nonce `base_nonce`
/// * A sequence number (initially 0)
///
/// The Secret Export parameters consist of:
///
/// * The HPKE ciphersuite in use
/// * An `exporter_secret` used for the Secret Export interface; see [`Context_Export`].
///
/// All these parameters except the AEAD sequence number are constant.
/// The sequence number provides nonce uniqueness: The nonce used for
/// each encryption or decryption operation is the result of XORing
/// `base_nonce` with the current sequence number, encoded as a big-endian
/// integer of the same length as `base_nonce`. Implementations MAY use a
/// sequence number that is shorter than the nonce length (padding on the left
/// with zero), but MUST raise an error if the sequence number overflows. The AEAD
/// algorithm produces ciphertext that is Nt bytes longer than the plaintext.
/// Nt = 16 for AEAD algorithms defined in this document.
///
/// Encryption is unidirectional from sender to recipient. The sender's
/// context can encrypt a plaintext `pt` with associated data `aad` as
/// follows:
///
/// ```text
/// def ContextS.Seal(aad, pt):
///   ct = Seal(self.key, self.ComputeNonce(self.seq), aad, pt)
///   self.IncrementSeq()
///   return ct
/// ```
///
/// The sender's context MUST NOT be used for decryption. Similarly, the recipient's
/// context MUST NOT be used for encryption. Higher-level protocols re-using the HPKE
/// key exchange for more general purposes can derive separate keying material as
/// needed using use the Secret Export interface; see [`Context_Export`] and
/// [Bidirectional Encryption](`crate#bidirectional-encryption`) for more details.
///
/// It is up to the application to ensure that encryptions and decryptions are
/// done in the proper sequence, so that encryption and decryption nonces align.
/// If [`ContextS_Seal()`] or [`ContextR_Open()`] would cause the `seq` field to
/// overflow, then the implementation MUST fail with an error. (In the pseudocode
/// `Context<ROLE>.IncrementSeq()` fails with an error when `seq` overflows,
/// which causes [`ContextS_Seal()`] and [`ContextR_Open()`] to fail accordingly.)
/// Note that the internal `Seal()` and `Open()`
/// calls inside correspond to the context's [`AEAD`] algorithm.
pub fn ContextS_Seal(
    aead_id: AEAD,
    context: Context,
    aad: &[u8],
    pt: &[u8],
) -> Result<(Ciphertext, Context), HpkeError> {
    let (key, base_nonce, seq, exp) = context;
    let nonce = ComputeNonce(aead_id, &base_nonce, seq);
    let ct = AeadSeal(aead_id, &key, &nonce, aad, pt)?;
    let seq = IncrementSeq(aead_id, seq)?;
    Ok((ct, (key, base_nonce, seq, exp)))
}

/// ## Stateful open.
///
/// See [ContextR.Open](`ContextS_Seal`) for more details.
///
/// The recipient's context can decrypt a ciphertext `ct` with associated
/// data `aad` as follows:
///
/// ```text
/// def ContextR.Open(aad, ct):
///   pt = Open(self.key, self.ComputeNonce(self.seq), aad, ct)
///   if pt == OpenError:
///     raise OpenError
///   self.IncrementSeq()
///   return pt
/// ```
pub fn ContextR_Open(
    aead_id: AEAD,
    context: Context,
    aad: &[u8],
    ct: &[u8],
) -> Result<(Vec<u8>, Context), HpkeError> {
    let (key, base_nonce, seq, exp) = context;
    let nonce = ComputeNonce(aead_id, &base_nonce, seq);
    let pt = AeadOpen(aead_id, &key, &nonce, aad, ct)?;
    let seq = IncrementSeq(aead_id, seq)?;
    Ok((pt, (key, base_nonce, seq, exp)))
}

/// ### Increment Sequence
///
/// Each encryption or decryption operation increments the sequence number for
/// the context in use.
///
/// ``` text
/// def Context<ROLE>.IncrementSeq():
///   if self.seq >= (1 << (8*Nn)) - 1:
///     raise MessageLimitReachedError
///   self.seq += 1
/// ```
pub fn IncrementSeq(aead_id: AEAD, seq: SequenceCounter) -> Result<SequenceCounter, HpkeError> {
    if seq as u128 >= (1u128 << (8 * Nn(aead_id))) - 1u128 {
        Err(HpkeError::MessageLimitReachedError)
    } else {
        Ok(seq + 1u32)
    }
}

/// ## Secret Export
///
/// HPKE provides an interface for exporting secrets from the encryption context
/// using a variable-length PRF, similar to the TLS 1.3 exporter interface
/// (see [RFC8446], Section 7.5). This interface takes as input a context
/// string `exporter_context` and a desired length `L` in bytes, and produces
/// a secret derived from the internal exporter secret using the corresponding
/// KDF Expand function. For the KDFs defined in this specification, `L` has
/// a maximum value of `255*Nh`. Future specifications which define new KDFs
/// MUST specify a bound for `L`.
///
/// The `exporter_context` field has a maximum length that depends on the KDF
/// itself, on the definition of `LabeledExpand()`, and on the constant labels
/// used together with them. See [KDF Input Length](mod@crate::hpke::kdf#input-length-restrictions)
/// for precise limits on this length.
///
/// ```text
/// def Context.Export(exporter_context, L):
///   return LabeledExpand(self.exporter_secret, "sec",
///                        exporter_context, L)
/// ```
///
/// Applications that do not use the encryption API in [`ContextS_Seal`] can use
/// the export-only AEAD ID `0xFFFF` when computing the key schedule. Such
/// applications can avoid computing the `key` and `base_nonce` values in the
/// key schedule, as they are not used by the Export interface described above.
///
/// [RFC8446]: https://www.rfc-editor.org/info/rfc8446
pub fn Context_Export(
    config: HPKEConfig,
    context: &Context,
    exporter_context: Vec<u8>,
    L: usize,
) -> HpkeBytesResult {
    let (_, _, _, exporter_secret) = context;
    let HPKEConfig(_, _, kdf_id, _) = config;
    LabeledExpand(
        kdf_id,
        suite_id(config),
        exporter_secret,
        sec_label(),
        &exporter_context,
        L,
    )
}

// === Singe-Shot API ===

/// ## Encryption
///
/// In many cases, applications encrypt only a single message to a recipient's
/// public key. This section provides templates for HPKE APIs that implement
/// stateless "single-shot" encryption and decryption using APIs specified in
/// [`SetupBaseS()`] and [`ContextS_Seal`]:
///
/// ```text
/// def Seal<MODE>(pkR, info, aad, pt, ...):
///   enc, ctx = Setup<MODE>S(pkR, info, ...)
///   ct = ctx.Seal(aad, pt)
///   return enc, ct
/// ```
///
/// The `MODE` template parameter is one of Base, PSK, Auth, or AuthPSK. The optional parameters
/// indicated by "..." depend on `MODE` and may be empty.
///
/// This function takes the `<MODE>` as argument in [`HPKEConfig`].
pub fn HpkeSeal(
    config: HPKEConfig,
    pkR: &HpkePublicKey,
    info: &Info,
    aad: &AdditionalData,
    ptxt: &[u8],
    psk: Option<&Psk>,
    psk_id: Option<&PskId>,
    skS: Option<&HpkePrivateKey>,
    randomness: Randomness,
) -> Result<HPKECiphertext, HpkeError> {
    let HPKEConfig(mode, _kem, _kdf, aead) = config;
    let (enc, (key, nonce, _, _)) = match mode {
        Mode::mode_base => SetupBaseS(config, pkR, info, randomness),
        Mode::mode_psk => SetupPSKS(config, pkR, info, psk.unwrap(), psk_id.unwrap(), randomness),
        Mode::mode_auth => SetupAuthS(config, pkR, info, skS.unwrap(), randomness),
        Mode::mode_auth_psk => SetupAuthPSKS(
            config,
            pkR,
            info,
            psk.unwrap(),
            psk_id.unwrap(),
            skS.unwrap(),
            randomness,
        ),
    }?;
    let ct = AeadSeal(aead, &key, &nonce, aad, ptxt)?;
    Ok(HPKECiphertext(enc, ct))
}

/// ## Decryption
///
/// See [`HpkeSeal`] for more details.
///
/// ```text
/// def Open<MODE>(enc, skR, info, aad, ct, ...):
///   ctx = Setup<MODE>R(enc, skR, info, ...)
///   return ctx.Open(aad, ct)
/// ```
///
/// This function takes the `<MODE>` as argument in [`HPKEConfig`].
pub fn HpkeOpen(
    config: HPKEConfig,
    ctxt: &HPKECiphertext,
    skR: &HpkePrivateKey,
    info: &Info,
    aad: &AdditionalData,
    psk: Option<&Psk>,
    psk_id: Option<&PskId>,
    pkS: Option<&HpkePublicKey>,
) -> HpkeBytesResult {
    let HPKEConfig(mode, _kem, _kdf, aead) = config;
    let HPKECiphertext(enc, ct) = ctxt;

    let (key, nonce, _, _) = match mode {
        Mode::mode_base => SetupBaseR(config, enc, skR, info),
        Mode::mode_psk => SetupPSKR(config, enc, skR, info, psk.unwrap(), psk_id.unwrap()),
        Mode::mode_auth => SetupAuthR(config, enc, skR, info, pkS.unwrap()),
        Mode::mode_auth_psk => SetupAuthPSKR(
            config,
            enc,
            skR,
            info,
            psk.unwrap(),
            psk_id.unwrap(),
            pkS.unwrap(),
        ),
    }?;

    let ptxt = AeadOpen(aead, &key, &nonce, aad, ct)?;
    Ok(ptxt)
}

/// ## "single-shot" secret export sender
///
/// ```text
/// def SendExport<MODE>(pkR, info, exporter_context, L, ...):
///   enc, ctx = Setup<MODE>S(pkR, info, ...)
///   exported = ctx.Export(exporter_context, L)
///   return enc, exported
/// ```
pub fn SendExport(
    config: HPKEConfig,
    pkR: &HpkePublicKey,
    info: &Info,
    exporter_context: Vec<u8>,
    L: usize,
    psk: Option<&Psk>,
    psk_id: Option<&PskId>,
    skS: Option<&HpkePrivateKey>,
    randomness: Randomness,
) -> Result<HPKECiphertext, HpkeError> {
    let HPKEConfig(mode, _kem, _kdf, _aead) = config;
    let (enc, ctx) = match mode {
        Mode::mode_base => SetupBaseS(config, pkR, info, randomness),
        Mode::mode_psk => SetupPSKS(config, pkR, info, psk.unwrap(), psk_id.unwrap(), randomness),
        Mode::mode_auth => SetupAuthS(config, pkR, info, &skS.unwrap(), randomness),
        Mode::mode_auth_psk => SetupAuthPSKS(
            config,
            pkR,
            info,
            psk.unwrap(),
            psk_id.unwrap(),
            &skS.unwrap(),
            randomness,
        ),
    }?;
    let exported = Context_Export(config, &ctx, exporter_context, L)?;
    Ok(HPKECiphertext(enc, exported))
}

/// ## "single-shot" secret export receiver
///
/// ``` text
/// def ReceiveExport<MODE>(enc, skR, info, exporter_context, L, ...):
///   ctx = Setup<MODE>R(enc, skR, info, ...)
///   return ctx.Export(exporter_context, L)
/// ```
pub fn ReceiveExport(
    config: HPKEConfig,
    enc: &EncodedHpkePublicKeyIn,
    skR: &HpkePrivateKey,
    info: &Info,
    exporter_context: Vec<u8>,
    L: usize,
    psk: Option<&Psk>,
    psk_id: Option<&PskId>,
    pkS: Option<&HpkePublicKey>,
) -> HpkeBytesResult {
    let HPKEConfig(mode, _kem, _kdf, _aead) = config;

    let ctx = match mode {
        Mode::mode_base => SetupBaseR(config, enc, skR, info),
        Mode::mode_psk => SetupPSKR(config, enc, skR, info, psk.unwrap(), psk_id.unwrap()),
        Mode::mode_auth => SetupAuthR(config, enc, skR, info, pkS.unwrap()),
        Mode::mode_auth_psk => SetupAuthPSKR(
            config,
            enc,
            skR,
            info,
            psk.unwrap(),
            psk_id.unwrap(),
            pkS.unwrap(),
        ),
    }?;
    Context_Export(config, &ctx, exporter_context, L)
}
