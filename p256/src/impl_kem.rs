use libcrux_traits::kem::arrayref::*;

// The two kinds of data that are actually there
const SCALAR_LEN: usize = 32;
const POINT_LEN: usize = 64;

// The sorts of data that the Kem trait needs
const EK_LEN: usize = POINT_LEN;
const CT_LEN: usize = POINT_LEN;
const SS_LEN: usize = POINT_LEN;

const DK_LEN: usize = SCALAR_LEN;
const RAND_KEYGEN_LEN: usize = SCALAR_LEN;
const RAND_ENCAPS_LEN: usize = SCALAR_LEN;

impl Kem<EK_LEN, DK_LEN, CT_LEN, SS_LEN, RAND_KEYGEN_LEN, RAND_ENCAPS_LEN> for super::P256 {
    fn keygen(
        ek: &mut [u8; EK_LEN],
        dk: &mut [u8; DK_LEN],
        rand: &[u8; RAND_KEYGEN_LEN],
    ) -> Result<(), KeyGenError> {
        if !super::p256::validate_private_key(rand.as_slice()) {
            return Err(KeyGenError::InvalidRandomness);
        }

        dk.copy_from_slice(rand.as_slice());
        if !super::p256::dh_initiator(ek, dk) {
            return Err(KeyGenError::Unknown);
        }

        Ok(())
    }

    fn encaps(
        ct: &mut [u8; CT_LEN],
        ss: &mut [u8; SS_LEN],
        ek: &[u8; EK_LEN],
        rand: &[u8; RAND_ENCAPS_LEN],
    ) -> Result<(), EncapsError> {
        if !super::p256::validate_public_key(ek) {
            return Err(EncapsError::InvalidEncapsKey);
        }

        if !super::p256::validate_private_key(rand.as_slice()) {
            return Err(EncapsError::InvalidRandomness);
        }

        if !super::p256::dh_responder(ss, ek, rand) {
            return Err(EncapsError::Unknown);
        }

        if !super::p256::dh_initiator(ct, rand) {
            return Err(EncapsError::Unknown);
        }

        Ok(())
    }

    fn decaps(
        ss: &mut [u8; SS_LEN],
        ct: &[u8; CT_LEN],
        dk: &[u8; DK_LEN],
    ) -> Result<(), DecapsError> {
        if !super::p256::validate_public_key(ct) {
            return Err(DecapsError::InvalidCiphertext);
        }

        if !super::p256::validate_private_key(dk.as_slice()) {
            return Err(DecapsError::InvalidDecapsKey);
        }

        if !super::p256::dh_responder(ss, ct, dk) {
            return Err(DecapsError::Unknown);
        }

        Ok(())
    }
}

libcrux_traits::kem::slice::impl_trait!(super::P256 => EK_LEN, DK_LEN, CT_LEN, SS_LEN, RAND_KEYGEN_LEN, RAND_ENCAPS_LEN);
