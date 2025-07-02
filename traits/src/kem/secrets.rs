use libcrux_secrets::{Classify, Declassify};

use super::owned;

pub use owned::{DecapsError, EncapsError, KeyGenError};

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
    fn keygen(
        rand: &[u8; RAND_KEYGEN_LEN],
    ) -> Result<
        (
            impl Declassify<Declassified = [u8; DK_LEN]>,
            impl Declassify<Declassified = [u8; EK_LEN]>,
        ),
        KeyGenError,
    >;

    /// Encapsulate a shared secret towards a given encapsulation key.
    fn encaps(
        ek: &[u8; EK_LEN],
        rand: &[u8; RAND_ENCAPS_LEN],
    ) -> Result<
        (
            impl Declassify<Declassified = [u8; SS_LEN]>,
            impl Declassify<Declassified = [u8; CT_LEN]>,
        ),
        EncapsError,
    >;

    /// Decapsulate a shared secret.
    fn decaps(
        ct: &[u8; CT_LEN],
        dk: &[u8; DK_LEN],
    ) -> Result<impl Declassify<Declassified = [u8; SS_LEN]>, DecapsError>;
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
    fn keygen(
        rand: &[u8; RAND_KEYGEN_LEN],
    ) -> Result<
        (
            impl Declassify<Declassified = [u8; DK_LEN]>,
            impl Declassify<Declassified = [u8; EK_LEN]>,
        ),
        KeyGenError,
    > {
        let (dk, ek) = <Self as owned::Kem<
            EK_LEN,
            DK_LEN,
            CT_LEN,
            SS_LEN,
            RAND_KEYGEN_LEN,
            RAND_ENCAPS_LEN,
        >>::keygen(rand)?;

        Ok((dk.classify(), ek.classify()))
    }

    fn encaps(
        ek: &[u8; EK_LEN],
        rand: &[u8; RAND_ENCAPS_LEN],
    ) -> Result<
        (
            impl Declassify<Declassified = [u8; SS_LEN]>,
            impl Declassify<Declassified = [u8; CT_LEN]>,
        ),
        EncapsError,
    > {
        let (ss, ct) = <Self as owned::Kem<
            EK_LEN,
            DK_LEN,
            CT_LEN,
            SS_LEN,
            RAND_KEYGEN_LEN,
            RAND_ENCAPS_LEN,
        >>::encaps(ek, rand)?;

        Ok((ss.classify(), ct.classify()))
    }

    fn decaps(
        ct: &[u8; CT_LEN],
        dk: &[u8; DK_LEN],
    ) -> Result<impl Declassify<Declassified = [u8; SS_LEN]>, DecapsError> {
        let ss = <Self as owned::Kem<
            EK_LEN,
            DK_LEN,
            CT_LEN,
            SS_LEN,
            RAND_KEYGEN_LEN,
            RAND_ENCAPS_LEN,
        >>::decaps(ct, dk)?;

        Ok(ss.classify())
    }
}
