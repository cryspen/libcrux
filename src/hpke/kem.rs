#![doc = include_str!("KEM_Readme.md")]
#![doc = include_str!("KEM_Security.md")]
#![allow(non_camel_case_types, non_snake_case)]

use libcrux_ecdh::{X25519PrivateKey, X25519PublicKey};

use super::errors::*;
use super::kdf::*;
use libcrux_kem::{
    Algorithm, X25519MlKem768Draft00PrivateKey, X25519MlKem768Draft00PublicKey,
    XWingKemDraft02PrivateKey, XWingKemDraft02PublicKey,
};
use libcrux_ml_kem::mlkem768;

/// ## Key Encapsulation Mechanisms (KEMs)
///
/// | Value  | KEM                        | Nsecret  | Nenc | Npk  | Nsk  | Auth | Reference               |
/// |:-------|:---------------------------|:---------|:-----|:-----|:-----|:-----|:------------------------|
/// | 0x0000 | (reserved)                 | N/A      | N/A  | N/A  | N/A  | yes  | N/A                     |
/// | 0x0010 | DHKEM(P-256, HKDF-SHA256)  | 32       | 65   | 65   | 32   | yes  | [NISTCurves], [RFC5869] |
/// | 0x0011 | DHKEM(P-384, HKDF-SHA384)  | 48       | 97   | 97   | 48   | yes  | [NISTCurves], [RFC5869] |
/// | 0x0012 | DHKEM(P-521, HKDF-SHA512)  | 64       | 133  | 133  | 66   | yes  | [NISTCurves], [RFC5869] |
/// | 0x0020 | DHKEM(X25519, HKDF-SHA256) | 32       | 32   | 32   | 32   | yes  | [RFC7748], [RFC5869]    |
/// | 0x0021 | DHKEM(X448, HKDF-SHA512)   | 64       | 56   | 56   | 56   | yes  | [RFC7748], [RFC5869]    |
/// | 0x0021 | DHKEM(X448, HKDF-SHA512)   | 64       | 1120 | 1216 | 2432 | no   | [xkyber]                |
///
/// The `Auth` column indicates if the KEM algorithm provides the [`AuthEncap()`]/[`AuthDecap()`]
/// interface and is therefore suitable for the Auth and AuthPSK modes. The meaning of all
/// other columns is explained below. All algorithms are suitable for the
/// PSK mode.
///
/// ### KEM Identifiers
///
/// The "HPKE KEM Identifiers" registry lists identifiers for key encapsulation
/// algorithms defined for use with HPKE. These identifiers are two-byte values,
/// so the maximum possible value is 0xFFFF = 65535.
///
/// Template:
///
/// * Value: The two-byte identifier for the algorithm
/// * KEM: The name of the algorithm
/// * Nsecret: The length in bytes of a KEM shared secret produced by the algorithm
/// * Nenc: The length in bytes of an encoded encapsulated key produced by the algorithm
/// * Npk: The length in bytes of an encoded public key for the algorithm
/// * Nsk: The length in bytes of an encoded private key for the algorithm
/// * Auth: A boolean indicating if this algorithm provides the [`AuthEncap()`]/[`AuthDecap()`] interface
/// * Reference: Where this algorithm is defined
///
/// [NISTCurves]: https://doi.org/10.6028/nist.fips.186-4
/// [RFC7748]: https://www.rfc-editor.org/info/rfc7748
/// [RFC5869]: https://www.rfc-editor.org/info/rfc5869
/// [xkyer]: https://datatracker.ietf.org/doc/html/draft-westerbaan-cfrg-hpke-xyber768d00-02
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum KEM {
    /// 0x0010
    DHKEM_P256_HKDF_SHA256,
    /// 0x0011
    DHKEM_P384_HKDF_SHA384,
    /// 0x0012
    DHKEM_P521_HKDF_SHA512,
    /// 0x0020
    DHKEM_X25519_HKDF_SHA256,
    /// 0x0021
    DHKEM_X448_HKDF_SHA512,
    /// 0x0030
    X25519Kyber768Draft00,
    /// 0x004D
    XWingDraft02,
}

/// [`u16`] value of the `kem_id`.
///
/// See [`KEM`] for details.
pub fn kem_value(kem_id: KEM) -> u16 {
    match kem_id {
        KEM::DHKEM_P256_HKDF_SHA256 => 0x0010,
        KEM::DHKEM_P384_HKDF_SHA384 => 0x0011,
        KEM::DHKEM_P521_HKDF_SHA512 => 0x0012,
        KEM::DHKEM_X25519_HKDF_SHA256 => 0x00020,
        KEM::DHKEM_X448_HKDF_SHA512 => 0x0021,
        KEM::X25519Kyber768Draft00 => 0x0030,
        KEM::XWingDraft02 => 0x004D,
    }
}

/// Get the [`KDF`] algorithm for the given `kem_id`.
///
/// See [`KEM`] for details.
fn kdf_for_kem(kem_id: KEM) -> KDF {
    match kem_id {
        KEM::DHKEM_P256_HKDF_SHA256 => KDF::HKDF_SHA256,
        KEM::DHKEM_P384_HKDF_SHA384 => KDF::HKDF_SHA384,
        KEM::DHKEM_P521_HKDF_SHA512 => KDF::HKDF_SHA512,
        KEM::DHKEM_X25519_HKDF_SHA256 => KDF::HKDF_SHA256,
        KEM::DHKEM_X448_HKDF_SHA512 => KDF::HKDF_SHA512,
        KEM::X25519Kyber768Draft00 => KDF::HKDF_SHA256,
        KEM::XWingDraft02 => KDF::HKDF_SHA256,
    }
}

/// Convert the KEM type to the KEM algorithm of libcrux.
fn kem_to_named_group(alg: KEM) -> Algorithm {
    match alg {
        KEM::DHKEM_P256_HKDF_SHA256 => Algorithm::Secp256r1,
        KEM::DHKEM_P384_HKDF_SHA384 => Algorithm::Secp384r1,
        KEM::DHKEM_P521_HKDF_SHA512 => Algorithm::Secp521r1,
        KEM::DHKEM_X25519_HKDF_SHA256 => Algorithm::X25519,
        KEM::DHKEM_X448_HKDF_SHA512 => Algorithm::X448,
        KEM::X25519Kyber768Draft00 => Algorithm::X25519, // This is only used for DH operations
        KEM::XWingDraft02 => Algorithm::X25519,          // This is only used for DH operations
    }
}

/// Get the length of the shared secret.
///
/// See [`KEM`] for details.
pub fn Nsecret(kem_id: KEM) -> usize {
    match kem_id {
        KEM::DHKEM_P256_HKDF_SHA256 => 32,
        KEM::DHKEM_P384_HKDF_SHA384 => 48,
        KEM::DHKEM_P521_HKDF_SHA512 => 64,
        KEM::DHKEM_X25519_HKDF_SHA256 => 32,
        KEM::DHKEM_X448_HKDF_SHA512 => 64,
        KEM::X25519Kyber768Draft00 => 64,
        KEM::XWingDraft02 => 32,
    }
}

/// Get the length of the encoded encapsulated key.
///
/// See [`KEM`] for details.
pub fn Nenc(kem_id: KEM) -> usize {
    match kem_id {
        KEM::DHKEM_P256_HKDF_SHA256 => 65,
        KEM::DHKEM_P384_HKDF_SHA384 => 97,
        KEM::DHKEM_P521_HKDF_SHA512 => 133,
        KEM::DHKEM_X25519_HKDF_SHA256 => 32,
        KEM::DHKEM_X448_HKDF_SHA512 => 56,
        KEM::X25519Kyber768Draft00 => 1120,
        KEM::XWingDraft02 => 1120,
    }
}

/// Get the length of the private key.
///
/// See [`KEM`] for details.
pub fn Nsk(kem_id: KEM) -> usize {
    match kem_id {
        KEM::DHKEM_P256_HKDF_SHA256 => 32,
        KEM::DHKEM_P384_HKDF_SHA384 => 48,
        KEM::DHKEM_P521_HKDF_SHA512 => 66,
        KEM::DHKEM_X25519_HKDF_SHA256 => 32,
        KEM::DHKEM_X448_HKDF_SHA512 => 56,
        KEM::X25519Kyber768Draft00 => 2432,
        KEM::XWingDraft02 => 2464,
    }
}

/// Get the length of the encoded public key.
///
/// See [`KEM`] for details.
pub fn Npk(kem_id: KEM) -> usize {
    match kem_id {
        KEM::DHKEM_P256_HKDF_SHA256 => 65,
        KEM::DHKEM_P384_HKDF_SHA384 => 97,
        KEM::DHKEM_P521_HKDF_SHA512 => 133,
        KEM::DHKEM_X25519_HKDF_SHA256 => 32,
        KEM::DHKEM_X448_HKDF_SHA512 => 56,
        KEM::X25519Kyber768Draft00 => 1216,
        KEM::XWingDraft02 => 1216,
    }
}

/// The length in bytes of a Diffie-Hellman shared secret produced by [`DH()`].
///
/// |                | [`Ndh`] |
/// | -------------- | ------- |
/// | P-256          | 32      |
/// | P-384          | 48      |
/// | P-521          | 66      |
/// | X25519         | 32      |
/// | X448           | 56      |
/// | X448Kyber768   | 32      |
pub fn Ndh(kem_id: KEM) -> usize {
    match kem_id {
        KEM::DHKEM_P256_HKDF_SHA256 => 32,
        KEM::DHKEM_P384_HKDF_SHA384 => 48,
        KEM::DHKEM_P521_HKDF_SHA512 => 66,
        KEM::DHKEM_X25519_HKDF_SHA256 => 32,
        KEM::DHKEM_X448_HKDF_SHA512 => 56,
        KEM::X25519Kyber768Draft00 => 32,
        KEM::XWingDraft02 => 32,
    }
}

pub type PrivateKey = Vec<u8>;
pub type PublicKey = Vec<u8>;
pub type KeyPair = (PrivateKey, PublicKey);
pub type PublicKeyIn = [u8];
pub type PrivateKeyIn = [u8];
pub type SharedSecret = Vec<u8>;
pub type SerializedPublicKey = Vec<u8>;
pub type Randomness = Vec<u8>;

pub type EncapResult = Result<(SharedSecret, SerializedPublicKey), HpkeError>;

// === Label ===

/// "dkp_prk"
fn dkp_prk_label() -> Vec<u8> {
    vec![0x64u8, 0x6bu8, 0x70u8, 0x5fu8, 0x70u8, 0x72u8, 0x6bu8]
}

/// "eae_prk"
fn eae_prk_label() -> Vec<u8> {
    vec![0x65u8, 0x61u8, 0x65u8, 0x5fu8, 0x70u8, 0x72u8, 0x6bu8]
}

/// "sk"
fn sk_label() -> Vec<u8> {
    vec![0x73u8, 0x6bu8]
}

/// "candidate"
fn candidate_label() -> Vec<u8> {
    vec![
        0x63u8, 0x61u8, 0x6eu8, 0x64u8, 0x69u8, 0x64u8, 0x61u8, 0x74u8, 0x65u8,
    ]
}

/// "shared_secret"
fn shared_secret_label() -> Vec<u8> {
    vec![
        0x73u8, 0x68u8, 0x61u8, 0x72u8, 0x65u8, 0x64u8, 0x5fu8, 0x73u8, 0x65u8, 0x63u8, 0x72u8,
        0x65u8, 0x74u8,
    ]
}

/// Get an empty byte sequence.
fn empty() -> Vec<u8> {
    vec![]
}

/// Get the label for the KEM with the cipher suite ID.
/// "KEM"
fn suite_id(alg: KEM) -> Vec<u8> {
    let mut suite_id = vec![0x4bu8, 0x45u8, 0x4du8]; // "KEM"
    suite_id.extend_from_slice(&kem_value(alg).to_be_bytes());
    suite_id
}

/// For the variants of DHKEM defined in this document, the size [`Nsecret`] of the
/// KEM shared secret is equal to the output length of the hash function
/// underlying the KDF. For P-256, P-384 and P-521, the size `Ndh` of the
/// Diffie-Hellman shared secret is equal to 32, 48, and 66, respectively,
/// corresponding to the x-coordinate of the resulting elliptic curve point.
/// For X25519 and X448, the size [`Ndh`] of is equal to 32 and 56, respectively.
fn shared_secret_from_dh(alg: KEM, mut secret: Vec<u8>) -> Result<SharedSecret, HpkeError> {
    match alg {
        KEM::DHKEM_P256_HKDF_SHA256 => Ok(secret.drain(0..Ndh(alg)).collect()),
        KEM::DHKEM_P384_HKDF_SHA384 => Ok(secret.drain(0..Ndh(alg)).collect()),
        KEM::DHKEM_P521_HKDF_SHA512 => Ok(secret.drain(0..Ndh(alg)).collect()),
        KEM::DHKEM_X25519_HKDF_SHA256 => Ok(secret),
        KEM::DHKEM_X448_HKDF_SHA512 => Ok(secret),
        KEM::X25519Kyber768Draft00 => {
            // This is only the x25519 part.
            Ok(secret)
        }
        KEM::XWingDraft02 => {
            // This is only the x25519 part.
            Ok(secret)
        }
    }
}

/// Perform a non-interactive Diffie-Hellman exchange using the private key
/// `skX` and public key `pkY` to produce a Diffie-Hellman shared
/// secret of length `Ndh`. This function can raise a
/// [`ValidationError`](`HpkeError::ValidationError`) as described in
/// [validation](#validation-of-inputs-and-outputs).
pub fn DH(alg: KEM, sk: &PrivateKeyIn, pk: &PublicKeyIn) -> Result<SharedSecret, HpkeError> {
    match crate::ecdh::derive(kem_to_named_group(alg).try_into().unwrap(), pk, sk) {
        Ok(secret) => shared_secret_from_dh(alg, secret),
        Err(_) => Err(HpkeError::ValidationError),
    }
}

fn pk(alg: KEM, sk: &PrivateKeyIn) -> Result<PublicKey, HpkeError> {
    match crate::kem::secret_to_public(kem_to_named_group(alg), sk) {
        Ok(pk) => Ok(pk),
        Err(_) => Err(HpkeError::ValidationError),
    }
}

/// Prepend 0x04 to the byte sequence.
fn nist_curve_to_uncompressed(pk: PublicKey) -> PublicKey {
    let mut out = vec![0x04u8];
    out.extend_from_slice(&pk);
    out
}

/// Produce a byte string of length `Npk` encoding the public key `pkX`.
///
/// For P-256, P-384 and P-521, the [`SerializePublicKey()`] function of the
/// KEM performs the uncompressed Elliptic-Curve-Point-to-Octet-String
/// conversion according to [SECG]. [`DeserializePublicKey()`] performs the
/// uncompressed Octet-String-to-Elliptic-Curve-Point conversion.
///
/// For X25519 and X448, the `SerializePublicKey()` and `DeserializePublicKey()`
/// functions are the identity function, since these curves already use
/// fixed-length byte strings for public keys.
///
/// Some deserialized public keys MUST be validated before they can be used.
///
/// [secg]: https://secg.org/sec1-v2.pdf
pub fn SerializePublicKey(alg: KEM, pk: PublicKey) -> PublicKey {
    match alg {
        KEM::DHKEM_P256_HKDF_SHA256 => nist_curve_to_uncompressed(pk),
        KEM::DHKEM_P384_HKDF_SHA384 => nist_curve_to_uncompressed(pk),
        KEM::DHKEM_P521_HKDF_SHA512 => nist_curve_to_uncompressed(pk),
        KEM::DHKEM_X25519_HKDF_SHA256 => pk,
        KEM::DHKEM_X448_HKDF_SHA512 => pk,
        KEM::X25519Kyber768Draft00 => pk, // This must have been encoded before
        KEM::XWingDraft02 => pk,          // This must have been encoded before
    }
}

/// Remove the leading 0x04 from the public key.
fn nist_curve_from_uncompressed(pk: &PublicKeyIn) -> Vec<u8> {
    if pk[0] == 0x04 && pk.len() > 64 {
        pk[1..].to_vec()
    } else {
        pk.to_vec()
    }
}

/// Parse a byte string of length `Npk` to recover a
/// public key. This function can raise a `DeserializeError` error upon `pkXm`
/// deserialization failure.
pub fn DeserializePublicKey(alg: KEM, enc: &[u8]) -> HpkeBytesResult {
    Ok(match alg {
        KEM::DHKEM_P256_HKDF_SHA256 => nist_curve_from_uncompressed(enc),
        KEM::DHKEM_P384_HKDF_SHA384 => nist_curve_from_uncompressed(enc),
        KEM::DHKEM_P521_HKDF_SHA512 => nist_curve_from_uncompressed(enc),
        KEM::DHKEM_X25519_HKDF_SHA256 => enc.to_vec(),
        KEM::DHKEM_X448_HKDF_SHA512 => enc.to_vec(),
        KEM::X25519Kyber768Draft00 => enc.to_vec(), // Deserialization must be done later
        KEM::XWingDraft02 => enc.to_vec(),          // Deserialization must be done later
    })
}

/// ```text
/// def ExtractAndExpand(dh, kem_context):
///   eae_prk = LabeledExtract("", "eae_prk", dh)
///   shared_secret = LabeledExpand(eae_prk, "shared_secret",
///                                 kem_context, Nsecret)
///   return shared_secret
/// ```
fn ExtractAndExpand(
    alg: KEM,
    suite_id: Vec<u8>,
    dh: SharedSecret,
    kem_context: &[u8],
) -> HpkeBytesResult {
    let kdf = kdf_for_kem(alg);
    let eae_prk = LabeledExtract(kdf, suite_id.clone(), &empty(), eae_prk_label(), &dh)?;
    LabeledExpand(
        kdf,
        suite_id,
        &eae_prk,
        shared_secret_label(),
        kem_context,
        Nsecret(alg),
    )
}

fn I2OSP(counter: usize) -> Vec<u8> {
    vec![counter as u8]
}

/// For X25519 and X448, the `DeriveKeyPair()` function applies a KDF to the input:
///
/// ```text
/// def DeriveKeyPair(ikm):
///   dkp_prk = LabeledExtract("", "dkp_prk", ikm)
///   sk = LabeledExpand(dkp_prk, "sk", "", Nsk)
///   return (sk, pk(sk))
/// ```
pub fn DeriveKeyPairX(alg: KEM, ikm: &InputKeyMaterial) -> Result<KeyPair, HpkeError> {
    let kdf = kdf_for_kem(alg);
    let dkp_prk = LabeledExtract(kdf, suite_id(alg), &empty(), dkp_prk_label(), ikm)?;

    let sk = LabeledExpand(kdf, suite_id(alg), &dkp_prk, sk_label(), &empty(), Nsk(alg))?;

    match crate::kem::secret_to_public(kem_to_named_group(alg), &sk) {
        Ok(pk) => Result::<KeyPair, HpkeError>::Ok((sk, pk)),
        Err(_) => Result::<KeyPair, HpkeError>::Err(HpkeError::CryptoError),
    }
}

/// ### DeriveKeyPair
///
/// The keys that [`DeriveKeyPair()`] produces have only as much entropy as the provided
/// input keying material. For a given KEM, the `ikm` parameter given to [`DeriveKeyPair()`] SHOULD
/// have length at least [`Nsk`], and SHOULD have at least [`Nsk`] bytes of entropy.
///
/// All invocations of KDF functions (such as [`LabeledExtract()`] or [`LabeledExpand()`]) in any
/// DHKEM's [`DeriveKeyPair()`] function use the DHKEM's associated KDF (as opposed to
/// the ciphersuite's KDF).
///
/// For P-256, P-384 and P-521, the [`DeriveKeyPair()`] function of the KEM performs
/// rejection sampling over field elements.
///
/// ```text
/// def DeriveKeyPair(ikm):
///   dkp_prk = LabeledExtract("", "dkp_prk", ikm)
///   sk = 0
///   counter = 0
///   while sk == 0 or sk >= order:
///     if counter > 255:
///       raise DeriveKeyPairError
///     bytes = LabeledExpand(dkp_prk, "candidate",
///                           I2OSP(counter, 1), Nsk)
///     bytes[0] = bytes[0] & bitmask
///     sk = OS2IP(bytes)
///     counter = counter + 1
///   return (sk, pk(sk))
/// ```
///
/// `order` is the order of the curve being used (see section D.1.2 of [NISTCurves]), and
/// is listed below for completeness.
///
/// ```text
/// P-256:
/// 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
///
/// P-384:
/// 0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf
///   581a0db248b0a77aecec196accc52973
///
/// P-521:
/// 0x01ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
///   fa51868783bf2f966b7fcc0148f709a5d03bb5c9b8899c47aebb6fb71e91386409
/// ```
///
/// `bitmask` is defined to be 0xFF for P-256 and P-384, and 0x01 for P-521.
/// The precise likelihood of `DeriveKeyPair()` failing with DeriveKeyPairError
/// depends on the group being used, but it is negligibly small in all cases.
/// See [hpke errors](`mod@crate::hpke::errors`) for information about dealing with such failures.
///
/// For X25519 and X448, the [`DeriveKeyPair()`] function applies a KDF to the input:
///
/// ```text
/// def DeriveKeyPair(ikm):
///   dkp_prk = LabeledExtract("", "dkp_prk", ikm)
///   sk = LabeledExpand(dkp_prk, "sk", "", Nsk)
///   return (sk, pk(sk))
/// ```
///
/// [NISTCurves]: https://doi.org/10.6028/nist.fips.186-4
pub fn DeriveKeyPair(alg: KEM, ikm: &InputKeyMaterial) -> Result<KeyPair, HpkeError> {
    match alg {
        KEM::DHKEM_P256_HKDF_SHA256
        | KEM::DHKEM_P384_HKDF_SHA384
        | KEM::DHKEM_P521_HKDF_SHA512
        | KEM::DHKEM_X25519_HKDF_SHA256
        | KEM::DHKEM_X448_HKDF_SHA512 => {
            let kdf = kdf_for_kem(alg);
            let dkp_prk = LabeledExtract(kdf, suite_id(alg), &empty(), dkp_prk_label(), ikm)?;

            let named_group = kem_to_named_group(alg);
            let sk = if alg == KEM::DHKEM_X25519_HKDF_SHA256 || alg == KEM::DHKEM_X448_HKDF_SHA512 {
                LabeledExpand(kdf, suite_id(alg), &dkp_prk, sk_label(), &empty(), 32)?
            } else {
                let mut bitmask = 0xFFu8;
                if alg == KEM::DHKEM_P521_HKDF_SHA512 {
                    bitmask = 0x01u8;
                }
                let mut sk = Vec::new();
                for counter in 0..256 {
                    if sk.len() == 0 {
                        // Only keep looking if we didn't find one.
                        let mut bytes = LabeledExpand(
                            kdf,
                            suite_id(alg),
                            &dkp_prk,
                            candidate_label(),
                            &I2OSP(counter),
                            32,
                        )?;
                        bytes[0] = bytes[0] & bitmask;
                        // This check ensure sk != 0 or sk < order
                        if crate::ecdh::validate_scalar(named_group.try_into().unwrap(), &bytes)
                            .is_ok()
                        {
                            sk = bytes;
                        }
                    }
                }
                sk
            };
            if sk.len() == 0 {
                Result::<KeyPair, HpkeError>::Err(HpkeError::DeriveKeyPairError)
            } else {
                let pk = pk(alg, &sk)?;
                Ok((sk, pk))
            }
        }
        KEM::X25519Kyber768Draft00 => Err(HpkeError::UnsupportedAlgorithm),
        KEM::XWingDraft02 => {
            // Use SHAKE128 to expand the ikm
            let seed: [u8; 96] = crate::hacl::sha3::shake128(ikm);
            // Use the first 64 bytes to generate the ML-KEM key pair
            let (sk, pk) = mlkem768::generate_key_pair(
                seed[..64]
                    .try_into()
                    .map_err(|_| HpkeError::DeriveKeyPairError)?,
            )
            .into_parts();
            // Use the next 32 bytes to generate the X25519 key pair
            let (xsk, xpk) = DeriveKeyPair(KEM::DHKEM_X25519_HKDF_SHA256, &seed[..96])?;

            let private = XWingKemDraft02PrivateKey {
                sk_m: sk,
                sk_x: X25519PrivateKey(xsk.try_into().map_err(|_| HpkeError::DeriveKeyPairError)?),
                pk_x: X25519PublicKey(
                    xpk.clone()
                        .try_into()
                        .map_err(|_| HpkeError::DeriveKeyPairError)?,
                ),
            };
            let public = XWingKemDraft02PublicKey {
                pk_m: pk,
                pk_x: X25519PublicKey(xpk.try_into().map_err(|_| HpkeError::DeriveKeyPairError)?),
            };
            Ok((private.encode(), public.encode()))
        }
    }
}

/// Randomized algorithm to generate a key pair `(skX, pkX)`.
pub fn GenerateKeyPair(alg: KEM, randomness: Randomness) -> Result<KeyPair, HpkeError> {
    if randomness.len() != Nsecret(alg) {
        debug_assert!(
            false,
            "Invalid randomness. Got {}, expected {}",
            randomness.len(),
            Nsecret(alg)
        );
        Err(HpkeError::InvalidParameters)
    } else {
        match alg {
            KEM::DHKEM_P256_HKDF_SHA256
            | KEM::DHKEM_P384_HKDF_SHA384
            | KEM::DHKEM_P521_HKDF_SHA512
            | KEM::DHKEM_X25519_HKDF_SHA256
            | KEM::DHKEM_X448_HKDF_SHA512 => DeriveKeyPair(alg, &randomness),
            KEM::X25519Kyber768Draft00 => {
                let dkp_prk = LabeledExtract(
                    kdf_for_kem(alg),
                    suite_id(alg),
                    &empty(),
                    dkp_prk_label(),
                    &randomness,
                )?;
                let seed = LabeledExpand(
                    kdf_for_kem(alg),
                    suite_id(alg),
                    &dkp_prk,
                    sk_label(),
                    &empty(),
                    32 + 64,
                )?;
                let (xsk, xpk) = DeriveKeyPair(KEM::DHKEM_X25519_HKDF_SHA256, &seed[..32])?;
                let (sk, pk) =
                    mlkem768::generate_key_pair(seed[32..].try_into().unwrap()).into_parts();

                let private = X25519MlKem768Draft00PrivateKey {
                    mlkem: sk,
                    x25519: libcrux_ecdh::X25519PrivateKey(xsk.try_into().unwrap()),
                };
                let public = X25519MlKem768Draft00PublicKey {
                    mlkem: pk,
                    x25519: X25519PublicKey(xpk.try_into().unwrap()),
                };
                Ok((private.encode(), public.encode()))
            }
            KEM::XWingDraft02 => DeriveKeyPair(alg, &randomness),
        }
    }
}

/// ```text
/// def Encap(pkR):
///   skE, pkE = GenerateKeyPair()
///   dh = DH(skE, pkR)
///   enc = SerializePublicKey(pkE)
///
///   pkRm = SerializePublicKey(pkR)
///   kem_context = concat(enc, pkRm)
///
///   shared_secret = ExtractAndExpand(dh, kem_context)
/// ```
pub fn Encap(alg: KEM, pkR: &PublicKeyIn, randomness: Randomness) -> EncapResult {
    let (skE, pkE) = GenerateKeyPair(alg, randomness)?;
    let dh = DH(alg, &skE, pkR)?;
    let enc = SerializePublicKey(alg, pkE);

    let pkRm = SerializePublicKey(alg, pkR.to_vec());
    let mut kem_context = enc.clone();
    kem_context.extend_from_slice(&pkRm);

    let shared_secret = ExtractAndExpand(alg, suite_id(alg), dh, &kem_context)?;
    EncapResult::Ok((shared_secret, enc))
}

/// Kyber Encap
///
/// FIXME: vec conversions and unwraps
pub fn Kyber768Draft00_Encap(pkR: &PublicKeyIn, randomness: Randomness) -> EncapResult {
    let (ct, ss) = mlkem768::encapsulate(&pkR.try_into().unwrap(), randomness.try_into().unwrap());

    EncapResult::Ok((ss.as_ref().to_vec(), ct.as_ref().to_vec()))
}

/// Kyber Decap
///
/// FIXME: vec conversions and unwraps
pub fn Kyber768Draft00_Decap(skR: &PrivateKeyIn, enc: &[u8]) -> Result<SharedSecret, HpkeError> {
    Ok(mlkem768::decapsulate(&skR.try_into().unwrap(), &enc.try_into().unwrap()).to_vec())
}

/// ```text
/// def Decap(enc, skR):
///   pkE = DeserializePublicKey(enc)
///   dh = DH(skR, pkE)
///
///   pkRm = SerializePublicKey(pk(skR))
///   kem_context = concat(enc, pkRm)
///
///   shared_secret = ExtractAndExpand(dh, kem_context)
///   return shared_secret
/// ```
pub fn Decap(alg: KEM, enc: &[u8], skR: &PrivateKeyIn) -> Result<SharedSecret, HpkeError> {
    let pkE = DeserializePublicKey(alg, enc)?;
    let dh = DH(alg, skR, &pkE)?;

    let pkR = pk(alg, skR)?;
    let pkRm = SerializePublicKey(alg, pkR);
    let mut kem_context = enc.to_vec();
    kem_context.extend_from_slice(&pkRm);

    ExtractAndExpand(alg, suite_id(alg), dh, &kem_context)
}

/// ```text
/// def AuthEncap(pkR, skS):
///   skE, pkE = GenerateKeyPair()
///   dh = concat(DH(skE, pkR), DH(skS, pkR))
///   enc = SerializePublicKey(pkE)
///
///   pkRm = SerializePublicKey(pkR)
///   pkSm = SerializePublicKey(pk(skS))
///   kem_context = concat(enc, pkRm, pkSm)
///
///   shared_secret = ExtractAndExpand(dh, kem_context)
///   return shared_secret, enc
/// ```
pub fn AuthEncap(
    alg: KEM,
    pkR: &PublicKeyIn,
    skS: &PrivateKeyIn,
    randomness: Randomness,
) -> EncapResult {
    let (skE, pkE) = GenerateKeyPair(alg, randomness)?;
    let dhE = DH(alg, &skE, pkR)?;
    let dhS = DH(alg, skS, pkR)?;
    let mut dh = dhE;
    dh.extend_from_slice(&dhS);
    let enc = SerializePublicKey(alg, pkE);

    let pkRm = SerializePublicKey(alg, pkR.to_vec());
    let pkS = pk(alg, skS)?;
    let pkSm = SerializePublicKey(alg, pkS);
    let mut kem_context = enc.clone();
    kem_context.extend_from_slice(&pkRm);
    kem_context.extend_from_slice(&pkSm);

    let shared_secret = ExtractAndExpand(alg, suite_id(alg), dh, &kem_context)?;
    EncapResult::Ok((shared_secret, enc))
}

/// ```text
/// def AuthDecap(enc, skR, pkS):
///   pkE = DeserializePublicKey(enc)
///   dh = concat(DH(skR, pkE), DH(skR, pkS))
///
///   pkRm = SerializePublicKey(pk(skR))
///   pkSm = SerializePublicKey(pkS)
///   kem_context = concat(enc, pkRm, pkSm)
///
///   shared_secret = ExtractAndExpand(dh, kem_context)
///   return shared_secret
/// ```
pub fn AuthDecap(
    alg: KEM,
    enc: &[u8],
    skR: &PrivateKeyIn,
    pkS: &PublicKeyIn,
) -> Result<SharedSecret, HpkeError> {
    let pkE = DeserializePublicKey(alg, enc)?;
    let dhE = DH(alg, skR, &pkE)?;
    let dhS = DH(alg, skR, pkS)?;
    let mut dh = dhE;
    dh.extend_from_slice(&dhS);

    let pkR = pk(alg, skR)?;
    let pkRm = SerializePublicKey(alg, pkR);
    let pkSm = SerializePublicKey(alg, pkS.to_vec());
    let mut kem_context = enc.to_vec();
    kem_context.extend_from_slice(&pkRm);
    kem_context.extend_from_slice(&pkSm);

    ExtractAndExpand(alg, suite_id(alg), dh, &kem_context)
}

#[test]
fn derive_x25519() {
    use std::num::ParseIntError;

    fn from_hex(s: &str) -> Vec<u8> {
        debug_assert!(s.len() % 2 == 0);
        let b: Result<Vec<u8>, ParseIntError> = (0..s.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&s[i..i + 2], 16))
            .collect();
        b.expect("Error parsing hex string")
    }

    // A.1.1. test vector
    let ikm_e = from_hex("7268600d403fce431561aef583ee1613527cff655c1343f29812e66706df3234");
    let ikm_r = from_hex("6db9df30aa07dd42ee5e8181afdb977e538f5e1fec8a06223f33f7013e525037");
    let expected_sk_e =
        from_hex("52c4a758a802cd8b936eceea314432798d5baf2d7e9235dc084ab1b9cfa2f736");
    let expected_pk_e =
        from_hex("37fda3567bdbd628e88668c3c8d7e97d1d1253b6d4ea6d44c150f741f1bf4431");
    let expected_sk_r =
        from_hex("4612c550263fc8ad58375df3f557aac531d26850903e55a9f23f21d8534e8ac8");
    let expected_pk_r =
        from_hex("3948cfe0ad1ddb695d780e59077195da6c56506b027329794ab02bca80815c4d");

    let (sk_e, pk_e) =
        DeriveKeyPair(KEM::DHKEM_X25519_HKDF_SHA256, &ikm_e).expect("Error deriving key pair");
    let (sk_r, pk_r) =
        DeriveKeyPair(KEM::DHKEM_X25519_HKDF_SHA256, &ikm_r).expect("Error deriving key pair");

    assert_eq!(expected_sk_e, sk_e);
    assert_eq!(expected_sk_r, sk_r);
    assert_eq!(expected_pk_e, pk_e);
    assert_eq!(expected_pk_r, pk_r);
}
