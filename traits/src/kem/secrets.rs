//! This module contains the trait and related errors for a KEM that takes array references as
//! arguments and returns results instead of writing to a mutable reference. Secret values use the
//! types from [libcrux-secrets](libcrux_secrets).

use libcrux_secrets::{Classify as _, DeclassifyRef as _, U8};

use super::owned;

// Re-export errors use in here
pub use owned::{DecapsError, EncapsError, KeyGenError};

/// A Key Encapsulation Mechanismd (KEM). This trait makes use of types suitable for checking
/// secret independence.
pub trait Kem<
    const EK_LEN: usize,
    const DK_LEN: usize,
    const CT_LEN: usize,
    const SS_LEN: usize,
    const RAND_KEYGEN_LEN: usize,
    const RAND_ENCAPS_LEN: usize,
>
{
    /// Generate a pair of encapsulation and decapsulation keys.
    fn keygen(rand: &[U8; RAND_KEYGEN_LEN]) -> Result<([U8; DK_LEN], [u8; EK_LEN]), KeyGenError>;

    /// Encapsulate a shared secret towards a given encapsulation key.
    fn encaps(
        ek: &[u8; EK_LEN],
        rand: &[U8; RAND_ENCAPS_LEN],
    ) -> Result<([U8; SS_LEN], [u8; CT_LEN]), EncapsError>;

    /// Decapsulate a shared secret.
    fn decaps(ct: &[u8; CT_LEN], dk: &[U8; DK_LEN]) -> Result<[U8; SS_LEN], DecapsError>;
}

impl<
        const EK_LEN: usize,
        const DK_LEN: usize,
        const CT_LEN: usize,
        const SS_LEN: usize,
        const RAND_KEYGEN_LEN: usize,
        const RAND_ENCAPS_LEN: usize,
        T: owned::Kem<EK_LEN, DK_LEN, CT_LEN, SS_LEN, RAND_KEYGEN_LEN, RAND_ENCAPS_LEN>,
    > Kem<EK_LEN, DK_LEN, CT_LEN, SS_LEN, RAND_KEYGEN_LEN, RAND_ENCAPS_LEN> for T
{
    fn keygen(rand: &[U8; RAND_KEYGEN_LEN]) -> Result<([U8; DK_LEN], [u8; EK_LEN]), KeyGenError> {
        let (dk, ek) = <Self as owned::Kem<
            EK_LEN,
            DK_LEN,
            CT_LEN,
            SS_LEN,
            RAND_KEYGEN_LEN,
            RAND_ENCAPS_LEN,
        >>::keygen(rand.declassify_ref())?;

        Ok((dk.classify(), ek))
    }

    fn encaps(
        ek: &[u8; EK_LEN],
        rand: &[U8; RAND_ENCAPS_LEN],
    ) -> Result<([U8; SS_LEN], [u8; CT_LEN]), EncapsError> {
        let (ss, ct) = <Self as owned::Kem<
            EK_LEN,
            DK_LEN,
            CT_LEN,
            SS_LEN,
            RAND_KEYGEN_LEN,
            RAND_ENCAPS_LEN,
        >>::encaps(ek, rand.declassify_ref())?;

        Ok((ss.classify(), ct))
    }

    fn decaps(ct: &[u8; CT_LEN], dk: &[U8; DK_LEN]) -> Result<[U8; SS_LEN], DecapsError> {
        let ss = <Self as owned::Kem<
            EK_LEN,
            DK_LEN,
            CT_LEN,
            SS_LEN,
            RAND_KEYGEN_LEN,
            RAND_ENCAPS_LEN,
        >>::decaps(ct, dk.declassify_ref())?;

        Ok(ss.classify())
    }
}
