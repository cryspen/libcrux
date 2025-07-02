use super::arrayref;

pub use arrayref::{DecapsError, EncapsError, KeyGenError};

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
    fn keygen(rand: &[u8; RAND_KEYGEN_LEN]) -> Result<([u8; DK_LEN], [u8; EK_LEN]), KeyGenError>;

    /// Encapsulate a shared secret towards a given encapsulation key.
    fn encaps(
        ek: &[u8; EK_LEN],
        rand: &[u8; RAND_ENCAPS_LEN],
    ) -> Result<([u8; SS_LEN], [u8; CT_LEN]), EncapsError>;

    /// Decapsulate a shared secret.
    fn decaps(ct: &[u8; CT_LEN], dk: &[u8; DK_LEN]) -> Result<[u8; SS_LEN], DecapsError>;
}

impl<
        const EK_LEN: usize,
        const DK_LEN: usize,
        const CT_LEN: usize,
        const SS_LEN: usize,
        const RAND_KEYGEN_LEN: usize,
        const RAND_ENCAPS_LEN: usize,
        T: arrayref::Kem<EK_LEN, DK_LEN, CT_LEN, SS_LEN, RAND_KEYGEN_LEN, RAND_ENCAPS_LEN>,
    > Kem<EK_LEN, DK_LEN, CT_LEN, SS_LEN, RAND_KEYGEN_LEN, RAND_ENCAPS_LEN> for T
{
    fn keygen(rand: &[u8; RAND_KEYGEN_LEN]) -> Result<([u8; DK_LEN], [u8; EK_LEN]), KeyGenError> {
        let mut dk = [0u8; DK_LEN];
        let mut ek = [0u8; EK_LEN];

        <Self as arrayref::Kem<
            EK_LEN,
            DK_LEN,
            CT_LEN,
            SS_LEN,
            RAND_KEYGEN_LEN,
            RAND_ENCAPS_LEN,
        >>::keygen(&mut ek, &mut dk, rand)?;

        Ok((dk, ek))
    }

    fn encaps(
        ek: &[u8; EK_LEN],
        rand: &[u8; RAND_ENCAPS_LEN],
    ) -> Result<([u8; SS_LEN], [u8; CT_LEN]), EncapsError> {
        let mut ss = [0u8; SS_LEN];
        let mut ct = [0u8; CT_LEN];

        <Self as arrayref::Kem<
            EK_LEN,
            DK_LEN,
            CT_LEN,
            SS_LEN,
            RAND_KEYGEN_LEN,
            RAND_ENCAPS_LEN,
        >>::encaps(&mut ct, &mut ss, ek, rand)?;

        Ok((ss, ct))
    }

    fn decaps(ct: &[u8; CT_LEN], dk: &[u8; DK_LEN]) -> Result<[u8; SS_LEN], DecapsError> {
        let mut ss = [0u8; SS_LEN];

        <Self as arrayref::Kem<
            EK_LEN,
            DK_LEN,
            CT_LEN,
            SS_LEN,
            RAND_KEYGEN_LEN,
            RAND_ENCAPS_LEN,
        >>::decaps(&mut ss, ct, dk)?;

        Ok(ss)
    }
}
