//! This module provides a trait for implementing Pre-Hash ML-DSA.
//!
//! As described in [Section 5.4](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.204.pdf#subsection.5.4)
//! of FIPS 204, any NIST-approved hash function or XOF can be used to
//!/perform the pre-hash of the message. This module implements the
//! pre-hash trait for SHAKE-128, with a digest length of 256 bytes.
use crate::{
    constants::CONTEXT_MAX_LEN, hash_functions::shake128::Xof, SigningError, VerificationError,
};

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

/// Binds the context string to an optional pre-hash OID identifying
/// the hash function or XOF used for pre-hashing.
pub(crate) struct DomainSeparationContext<'a> {
    context: &'a [u8],
    pre_hash_oid: Option<&'a PreHashOID>,
}

pub(crate) enum DomainSeparationError {
    ContextTooLongError,
}

impl<'a> DomainSeparationContext<'a> {
    /// `context` must be at most 255 bytes long.
    pub(crate) fn new(
        context: &'a [u8],
        pre_hash_oid: Option<&'a PreHashOID>,
    ) -> Result<Self, DomainSeparationError> {
        if context.len() > CONTEXT_MAX_LEN {
            Err(DomainSeparationError::ContextTooLongError)
        } else {
            Ok(Self {
                context,
                pre_hash_oid,
            })
        }
    }

    /// Returns the context, guaranteed to be at most 255 bytes long.
    pub fn context(&self) -> &[u8] {
        self.context
    }

    /// Returns the pre-hash OID, if any.
    pub fn pre_hash_oid(&self) -> Option<&PreHashOID> {
        self.pre_hash_oid
    }
}

impl From<DomainSeparationError> for SigningError {
    fn from(e: DomainSeparationError) -> SigningError {
        match e {
            DomainSeparationError::ContextTooLongError => SigningError::ContextTooLongError,
        }
    }
}

impl From<DomainSeparationError> for VerificationError {
    fn from(e: DomainSeparationError) -> VerificationError {
        match e {
            DomainSeparationError::ContextTooLongError => VerificationError::ContextTooLongError,
        }
    }
}
