//! This module provides a trait for implementing Pre-Hash ML-DSA.
//!
//! As described in [Section 5.4](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.204.pdf#subsection.5.4)
//! of FIPS 204, any NIST-approved hash function or XOF can be used to
//!/perform the pre-hash of the message. This module implements the
//! pre-hash trait for SHAKE-128, with a digest length of 256 bytes.
use crate::hash_functions::shake128::Xof;

pub(crate) const PRE_HASH_OID_LEN: usize = 11;
pub(crate) type PreHashOID = [u8; PRE_HASH_OID_LEN];

pub(crate) trait PreHash<const DIGEST_LEN: usize> {
    /// The object identifier (OID) of the hash function or XOF used
    /// to perform the pre-hashing of the message.
    fn oid() -> PreHashOID;

    /// Used to derive the pre-hash PH of the message before signing.
    fn hash(message: &[u8]) -> [u8; DIGEST_LEN];
}

#[allow(non_camel_case_types)]
/// An implementation of the pre-hash trait for the SHAKE-128 XOF with
/// digest length 256 bytes.
pub(crate) struct SHAKE128_PH();

impl PreHash<256> for SHAKE128_PH {
    fn oid() -> PreHashOID {
        [
            0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x0b,
        ]
    }

    fn hash(message: &[u8]) -> [u8; 256] {
        let mut output = [0u8; 256];
        crate::hash_functions::portable::Shake128::shake128(message, &mut output);

        output
    }
}
