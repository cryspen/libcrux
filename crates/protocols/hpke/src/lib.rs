//! This implements the work-in-progress Hybrid Public Key Encryption RFC.
//! https://cfrg.github.io/draft-irtf-cfrg-hpke/draft-irtf-cfrg-hpke.html
//!

#[cfg(feature = "serialization")]
use serde::{Deserialize, Serialize};

pub mod aead;
mod aead_impl;
pub mod dh_kem;
mod hkdf;
pub mod kdf;
pub mod kem;

mod util;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum HPKEError {
    OpenError,
    InvalidConfig,
    InvalidInput,
}

/// An HPKE public key is a byte vector.
#[derive(Debug, PartialEq, Clone, Default)]
#[cfg_attr(feature = "serialization", derive(Serialize, Deserialize))]
pub struct HPKEPublicKey {
    value: Vec<u8>,
}

/// An HPKE private key is a byte vector.
#[derive(Default)]
#[cfg_attr(feature = "serialization", derive(Serialize, Deserialize))]
pub struct HPKEPrivateKey {
    value: Vec<u8>,
}

/// An HPKE key pair has an HPKE private and public key.
#[derive(Debug, Default)]
#[cfg_attr(feature = "serialization", derive(Serialize, Deserialize))]
pub struct HPKEKeyPair {
    private_key: HPKEPrivateKey,
    public_key: HPKEPublicKey,
}

/// HPKE supports four modes.
/// The `Base` mode i
#[derive(PartialEq, Copy, Clone, Debug)]
#[repr(u8)]
pub enum Mode {
    Base = 0x00,
    Psk = 0x01,
    Auth = 0x02,
    AuthPsk = 0x03,
}

impl From<u16> for Mode {
    fn from(x: u16) -> Mode {
        match x {
            0x00 => Mode::Base,
            0x01 => Mode::Psk,
            0x02 => Mode::Auth,
            0x03 => Mode::AuthPsk,
            _ => panic!("Unknown HPKE Mode {}", x),
        }
    }
}

/// Type alias for encapsulated secrets.
/// A byte vector.
type EncapsulatedSecret = Vec<u8>;

/// Type alias for ciphertexts.
/// A byte vector.
type Ciphertext = Vec<u8>;

/// Type alias for plain text.
/// A byte vector.
type Plaintext = Vec<u8>;

/// The HPKE context.
/// Note that the RFC currently doesn't define this.
/// Also see https://github.com/cfrg/draft-irtf-cfrg-hpke/issues/161.
pub struct Context<'a> {
    key: Vec<u8>,
    nonce: Vec<u8>,
    exporter_secret: Vec<u8>,
    sequence_number: u32,
    hpke: &'a Hpke,
}

impl<'a> std::fmt::Debug for Context<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Context {{\n  key: {:?}\n  nonce: {:?}\n exporter_secret: {:?}\n seq no: {:?}\n}}",
            self.key, self.nonce, self.exporter_secret, self.sequence_number
        )
    }
}

impl<'a> Context<'a> {
    /// 5.2. Encryption and Decryption
    ///
    /// Takes the associated data and the plain text as byte slices and returns
    /// the ciphertext or an error.
    ///
    /// ```text
    /// def Context.Seal(aad, pt):
    ///   ct = Seal(self.key, self.ComputeNonce(self.seq), aad, pt)
    ///   self.IncrementSeq()
    ///   return ct
    /// ```
    pub fn seal(&mut self, aad: &[u8], plain_txt: &[u8]) -> Result<Ciphertext, HPKEError> {
        let ctxt = self
            .hpke
            .aead
            .seal(&self.key, &self.compute_nonce(), aad, plain_txt)?;
        self.increment_seq();
        Ok(ctxt)
    }

    /// 5.2. Encryption and Decryption
    ///
    /// Takes the associated data and the ciphertext as byte slices and returns
    /// the plain text or an error.
    ///
    /// ```text
    /// def Context.Open(aad, ct):
    ///   pt = Open(self.key, self.ComputeNonce(self.seq), aad, ct)
    ///   if pt == OpenError:
    ///     raise OpenError
    ///   self.IncrementSeq()
    ///   return pt
    /// ```
    pub fn open(&mut self, aad: &[u8], cipher_txt: &[u8]) -> Result<Plaintext, HPKEError> {
        let ptxt = self
            .hpke
            .aead
            .open(&self.key, &self.compute_nonce(), aad, cipher_txt)?;
        self.increment_seq();
        Ok(ptxt)
    }

    /// 5.3. Secret Export
    ///
    /// Takes a serialised exporter context as byte slice and a length for the
    /// output secret and returns an exporter secret as byte vector.
    ///
    /// ```text
    /// def Context.Export(exporter_context, L):
    ///  return LabeledExpand(self.exporter_secret, "sec", exporter_context, L)
    ///```
    pub fn export(&self, exporter_context: &[u8], length: usize) -> Vec<u8> {
        self.hpke.kdf.labeled_expand(
            &self.exporter_secret,
            &self.hpke.get_ciphersuite(),
            "sec",
            exporter_context,
            length,
        )
    }

    // TODO: not cool
    fn compute_nonce(&self) -> Vec<u8> {
        let seq = self.sequence_number.to_be_bytes();
        let mut enc_seq = vec![0u8; self.nonce.len() - seq.len()];
        enc_seq.append(&mut seq.to_vec());
        util::xor_bytes(&enc_seq, &self.nonce)
    }

    fn increment_seq(&mut self) {
        self.sequence_number += 1;
    }
}

/// The HPKE configuration struct.
/// This holds the configuration for HPKE but no state.
/// To use HPKE first instantiate the configuration with
/// `let hpke = Hpke::new(mode, kem_mode, kdf_mode, aead_mode)`.
/// Now one can use the `hpke` configuration.
#[derive(Debug)]
pub struct Hpke {
    mode: Mode,
    kem_id: kem::Mode,
    kdf_id: kdf::Mode,
    aead_id: aead::Mode,
    kem: kem::Kem,
    kdf: kdf::Kdf,
    aead: aead::Aead,
    nk: usize,
    nn: usize,
    nh: usize,
}

impl Hpke {
    /// Set up the configuration for HPKE.
    pub fn new(mode: Mode, kem_id: kem::Mode, kdf_id: kdf::Mode, aead_id: aead::Mode) -> Self {
        let kem = kem::Kem::new(kem_id);
        let kdf = kdf::Kdf::new(kdf_id);
        let aead = aead::Aead::new(aead_id);
        Self {
            mode,
            kem_id,
            kdf_id,
            aead_id,
            nk: aead.get_nk(),
            nn: aead.get_nn(),
            nh: kdf.get_nh(),
            kem,
            kdf,
            aead,
        }
    }

    /// Set up an HPKE sender.
    ///
    /// For the base and PSK modes this encapsulates the public key `pk_r`
    /// of the receiver.
    /// For the Auth and AuthPSK modes this encapsulates and authenticates
    /// the public key `pk_r` of the receiver with the senders secret key `sk_s`.
    ///
    /// The encapsulated secret is returned together with the context.
    /// If the secret key is missing in an authenticated mode, an error is returned.
    pub fn setup_sender(
        &self,
        pk_r: &HPKEPublicKey,
        info: &[u8],
        psk: Option<&[u8]>,
        psk_id: Option<&[u8]>,
        sk_s: Option<&HPKEPrivateKey>,
    ) -> Result<(EncapsulatedSecret, Context), HPKEError> {
        let (zz, enc) = match self.mode {
            Mode::Base | Mode::Psk => self.kem.encaps(&pk_r.value),
            Mode::Auth | Mode::AuthPsk => {
                let sk_s = match sk_s {
                    Some(s) => &s.value,
                    None => return Err(HPKEError::InvalidInput),
                };
                self.kem.auth_encaps(&pk_r.value, sk_s)
            }
        };
        Ok((
            enc,
            self.key_schedule(
                &zz,
                info,
                psk.unwrap_or_default(),
                psk_id.unwrap_or_default(),
            ),
        ))
    }

    /// Set up an HPKE receiver.
    ///
    /// For the base and PSK modes this decapsulates `enc` with the secret key
    /// `sk_r` of the receiver.
    /// For the Auth and AuthPSK modes this decapsulates and authenticates `enc`
    /// with the secret key `sk_r` of the receiver and the senders public key `pk_s`.
    ///
    /// The context based on the decapsulated values and, if present, the PSK is
    /// returned.
    /// If the secret key is missing in an authenticated mode, an error is returned.
    pub fn setup_receiver(
        &self,
        enc: &[u8],
        sk_r: &HPKEPrivateKey,
        info: &[u8],
        psk: Option<&[u8]>,
        psk_id: Option<&[u8]>,
        pk_s: Option<&HPKEPublicKey>,
    ) -> Result<Context, HPKEError> {
        let zz = match self.mode {
            Mode::Base | Mode::Psk => self.kem.decaps(enc, &sk_r.value),
            Mode::Auth | Mode::AuthPsk => {
                let pk_s = match pk_s {
                    Some(s) => &s.value,
                    None => return Err(HPKEError::InvalidInput),
                };
                self.kem.auth_decaps(enc, &sk_r.value, pk_s)
            }
        };
        Ok(self.key_schedule(
            &zz,
            info,
            psk.unwrap_or_default(),
            psk_id.unwrap_or_default(),
        ))
    }

    /// 6. Single-Shot APIs
    /// 6.1. Encryption and Decryption
    ///
    /// Single shot API to encrypt the bytes in `plain_text` to the public key
    /// `pk_r`.
    ///
    /// Returns the encapsulated secret and the ciphertext, or an error.
    #[allow(clippy::too_many_arguments)]
    pub fn seal(
        &self,
        pk_r: &HPKEPublicKey,
        info: &[u8],
        aad: &[u8],
        plain_txt: &[u8],
        psk: Option<&[u8]>,
        psk_id: Option<&[u8]>,
        sk_s: Option<&HPKEPrivateKey>,
    ) -> Result<(EncapsulatedSecret, Ciphertext), HPKEError> {
        let (enc, mut context) = self.setup_sender(pk_r, info, psk, psk_id, sk_s)?;
        let ctxt = context.seal(aad, plain_txt)?;
        Ok((enc, ctxt))
    }

    /// 6. Single-Shot APIs
    /// 6.1. Encryption and Decryption
    ///
    /// Single shot API to decrypt the bytes in `ct` with the private key `sk_r`.
    ///
    /// Returns the decrypted plain text, or an error.
    #[allow(clippy::too_many_arguments)]
    pub fn open(
        &self,
        enc: &[u8],
        sk_r: &HPKEPrivateKey,
        info: &[u8],
        aad: &[u8],
        ct: &[u8],
        psk: Option<&[u8]>,
        psk_id: Option<&[u8]>,
        pk_s: Option<&HPKEPublicKey>,
    ) -> Result<Plaintext, HPKEError> {
        let mut context = self.setup_receiver(enc, sk_r, info, psk, psk_id, pk_s)?;
        context.open(aad, ct)
    }

    /// 6. Single-Shot APIs
    /// 6.2. Secret Export
    ///
    /// Single shot API to derive an exporter secret for receiver with public key
    /// `pk_r`.
    ///
    /// Returns the encapsulated secret and the exporter secret for the given
    /// exporter context and length.
    #[allow(clippy::too_many_arguments)]
    pub fn send_export(
        &self,
        pk_r: &HPKEPublicKey,
        info: &[u8],
        psk: Option<&[u8]>,
        psk_id: Option<&[u8]>,
        sk_s: Option<&HPKEPrivateKey>,
        exporter_context: &[u8],
        length: usize,
    ) -> Result<(EncapsulatedSecret, Vec<u8>), HPKEError> {
        let (enc, context) = self.setup_sender(pk_r, info, psk, psk_id, sk_s)?;
        Ok((enc, context.export(exporter_context, length)))
    }

    /// 6. Single-Shot APIs
    /// 6.2. Secret Export
    ///
    /// Single shot API to derive an exporter secret for receiver with private key
    /// `sk_r`.
    ///
    /// Returns the exporter secret for the given exporter context and length.
    #[allow(clippy::too_many_arguments)]
    pub fn receiver_export(
        &self,
        enc: &[u8],
        sk_r: &HPKEPrivateKey,
        info: &[u8],
        psk: Option<&[u8]>,
        psk_id: Option<&[u8]>,
        pk_s: Option<&HPKEPublicKey>,
        exporter_context: &[u8],
        length: usize,
    ) -> Result<Vec<u8>, HPKEError> {
        let context = self.setup_receiver(enc, sk_r, info, psk, psk_id, pk_s)?;
        Ok(context.export(exporter_context, length))
    }

    #[inline]
    fn verify_psk_inputs(&self, psk: &[u8], psk_id: &[u8]) {
        let got_psk = !psk.is_empty();
        let got_psk_id = !psk_id.is_empty();
        if (got_psk && !got_psk_id) || (!got_psk && got_psk_id) {
            panic!("Inconsistent PSK inputs");
        }

        if got_psk && (self.mode == Mode::Base || self.mode == Mode::Auth) {
            panic!("PSK input provided when not needed");
        }
        if !got_psk && (self.mode == Mode::Psk || self.mode == Mode::AuthPsk) {
            panic!("Missing required PSK input");
        }
    }

    #[inline]
    fn get_ciphersuite(&self) -> Vec<u8> {
        util::concat(&[
            b"HPKE",
            &(self.kem_id as u16).to_be_bytes(),
            &(self.kdf_id as u16).to_be_bytes(),
            &(self.aead_id as u16).to_be_bytes(),
        ])
    }

    #[inline]
    fn get_key_schedule_context(&self, info: &[u8], psk_id: &[u8], suite_id: &[u8]) -> Vec<u8> {
        let psk_id_hash = self
            .kdf
            .labeled_extract(&[0], suite_id, "psk_id_hash", psk_id);
        let info_hash = self.kdf.labeled_extract(&[0], suite_id, "info_hash", info);
        util::concat(&[&[self.mode as u8], &psk_id_hash, &info_hash])
    }

    /// 5.1. Creating the Encryption Context
    /// Generate the HPKE context from the given input.
    ///
    /// ```text
    /// default_psk = ""
    /// default_psk_id = ""
    ///
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
    ///
    /// def KeySchedule(mode, shared_secret, info, psk, psk_id):
    ///   VerifyPSKInputs(mode, psk, psk_id)
    ///
    ///   psk_id_hash = LabeledExtract("", "psk_id_hash", psk_id)
    ///   info_hash = LabeledExtract("", "info_hash", info)
    ///   key_schedule_context = concat(mode, psk_id_hash, info_hash)
    ///
    ///   secret = LabeledExtract(shared_secret, "secret", psk)
    ///
    ///   key = LabeledExpand(secret, "key", key_schedule_context, Nk)
    ///   base_nonce = LabeledExpand(secret, "base_nonce", key_schedule_context, Nn)
    ///   exporter_secret = LabeledExpand(secret, "exp", key_schedule_context, Nh)
    ///
    ///   return Context(key, base_nonce, 0, exporter_secret)
    /// ```
    pub fn key_schedule(
        &self,
        shared_secret: &[u8],
        info: &[u8],
        psk: &[u8],
        psk_id: &[u8],
    ) -> Context {
        self.verify_psk_inputs(psk, psk_id);
        let suite_id = self.get_ciphersuite();
        let key_schedule_context = self.get_key_schedule_context(info, psk_id, &suite_id);
        let secret = self
            .kdf
            .labeled_extract(shared_secret, &suite_id, "secret", psk);

        let key =
            self.kdf
                .labeled_expand(&secret, &suite_id, "key", &key_schedule_context, self.nk);
        let base_nonce = self.kdf.labeled_expand(
            &secret,
            &suite_id,
            "base_nonce",
            &key_schedule_context,
            self.nn,
        );
        let exporter_secret =
            self.kdf
                .labeled_expand(&secret, &suite_id, "exp", &key_schedule_context, self.nh);

        Context {
            key,
            nonce: base_nonce,
            exporter_secret,
            sequence_number: 0,
            hpke: self,
        }
    }

    /// 4. Cryptographic Dependencies
    /// Randomized algorithm to generate a key pair `(skX, pkX)` for the KEM.
    /// This is equivalent to `derive_key_pair(get_random_vector(sk.len()))`
    ///
    /// Returns an `HPKEKeyPair`.
    pub fn generate_key_pair(&self) -> HPKEKeyPair {
        let (sk, pk) = self.kem.key_gen();
        HPKEKeyPair::new(sk, pk)
    }

    /// 7.1.2. DeriveKeyPair
    /// Derive a key pair for the used KEM with the given input key material.
    ///
    /// Returns `HPKEKeyPair`
    pub fn derive_key_pair(&self, ikm: &[u8]) -> HPKEKeyPair {
        let (pk, sk) = self.kem.derive_key_pair(ikm);
        HPKEKeyPair::new(sk, pk)
    }
}

impl HPKEKeyPair {
    /// Create a new HPKE key pair.
    /// Consumes the private and public key bytes.
    pub fn new(sk: Vec<u8>, pk: Vec<u8>) -> Self {
        Self {
            private_key: HPKEPrivateKey::new(sk),
            public_key: HPKEPublicKey::new(pk),
        }
    }

    /// Get a reference to the HPKE private key of this key pair.
    pub fn get_private_key_ref(&self) -> &HPKEPrivateKey {
        &self.private_key
    }

    /// Get a reference to the HPKE public key of this key pair.
    pub fn get_public_key_ref(&self) -> &HPKEPublicKey {
        &self.public_key
    }

    /// Split the key pair into the two keys
    pub fn into_keys(self) -> (HPKEPrivateKey, HPKEPublicKey) {
        (self.private_key, self.public_key)
    }

    /// Build a key pair from two keys
    pub fn from_keys(private_key: HPKEPrivateKey, public_key: HPKEPublicKey) -> Self {
        Self {
            private_key,
            public_key,
        }
    }
}

impl HPKEPrivateKey {
    /// Create a new HPKE private key.
    /// Consumes the private key bytes.
    pub fn new(b: Vec<u8>) -> Self {
        Self { value: b }
    }

    /// Get the raw key as byte slice.
    #[cfg(feature = "hazmat")]
    pub fn as_slice(&self) -> &[u8] {
        &self.value
    }
}

/// Hopefully constant time comparison of the two values as long as they have the
/// same length.
impl PartialEq for HPKEPrivateKey {
    fn eq(&self, other: &Self) -> bool {
        if self.value.len() != other.value.len() {
            return false;
        }

        let mut different_bits = 0u8;
        for (&byte_a, &byte_b) in self.value.iter().zip(other.value.iter()) {
            different_bits |= byte_a ^ byte_b;
        }
        (1u8 & ((different_bits.wrapping_sub(1)).wrapping_shr(8)).wrapping_sub(1)) == 0
    }
}

#[cfg(feature = "hazmat")]
impl std::fmt::Debug for HPKEPrivateKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        f.debug_struct("HPKEPrivateKey")
            .field("value", &"***")
            .finish()
    }
}

#[cfg(not(feature = "hazmat"))]
impl std::fmt::Debug for HPKEPrivateKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        f.debug_struct("HPKEPrivateKey")
            .field("value", &self.value)
            .finish()
    }
}

impl HPKEPublicKey {
    /// Create a new HPKE public key.
    /// Consumes the public key bytes.
    pub fn new(b: Vec<u8>) -> Self {
        Self { value: b }
    }

    /// Get the raw key as byte slice.
    pub fn as_slice(&self) -> &[u8] {
        &self.value
    }
}

pub mod test_util {
    // TODO: don't build for release
    impl<'a> super::Context<'_> {
        /// Get a reference to the key in the context.
        #[doc(hidden)]
        pub fn get_key_ref(&'a self) -> &'a [u8] {
            &self.key
        }
        /// Get a reference to the nonce in the context.
        #[doc(hidden)]
        pub fn get_nonce_ref(&'a self) -> &'a [u8] {
            &self.nonce
        }
        /// Get a reference to the exporter secret in the context.
        #[doc(hidden)]
        pub fn get_exporter_secret_ref(&'a self) -> &'a [u8] {
            &self.exporter_secret
        }
        /// Get a reference to the sequence number in the context.
        #[doc(hidden)]
        pub fn get_sequence_number(&self) -> u32 {
            self.sequence_number
        }
    }
}

impl From<aead::Error> for HPKEError {
    fn from(e: aead::Error) -> Self {
        match e {
            aead::Error::OpenError => HPKEError::OpenError,
            aead::Error::InvalidNonce => HPKEError::InvalidConfig,
            aead::Error::InvalidConfig => HPKEError::InvalidInput,
        }
    }
}
