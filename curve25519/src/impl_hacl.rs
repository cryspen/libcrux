use super::*;

/// Implementation of Curve25519 backed by Hacl.
pub struct HaclCurve25519;

impl Curve25519 for HaclCurve25519 {
    // The hacl::ecdh function requires all parameters to be 32 byte long, which we enforce using
    // types.
    #[inline(always)]
    fn secret_to_public(pk: &mut [u8; EK_LEN], sk: &[u8; DK_LEN]) {
        secret_to_public(pk, sk)
    }

    // The hacl::ecdh function requires all parameters to be 32 byte long, which we enforce using
    // types.
    #[inline(always)]
    fn ecdh(out: &mut [u8; SS_LEN], pk: &[u8; EK_LEN], sk: &[u8; DK_LEN]) -> Result<(), Error> {
        ecdh(out, pk, sk)
    }
}

// The hacl::ecdh function requires all parameters to be 32 byte long, which we enforce using
// types.
#[inline(always)]
pub fn secret_to_public(pk: &mut [u8; EK_LEN], sk: &[u8; DK_LEN]) {
    crate::hacl::secret_to_public(pk, sk)
}

// The hacl::ecdh function requires all parameters to be 32 byte long, which we enforce using
// types.
#[inline(always)]
pub fn ecdh(out: &mut [u8; SS_LEN], pk: &[u8; EK_LEN], sk: &[u8; DK_LEN]) -> Result<(), Error> {
    match crate::hacl::ecdh(out, sk, pk) {
        true => Ok(()),
        false => Err(Error),
    }
}
