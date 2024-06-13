/// ECDSA on P256
pub mod ecdsa {

    use libcrux_hacl::{
        Hacl_P256_ecdsa_sign_p256_sha2, Hacl_P256_ecdsa_sign_p256_sha384,
        Hacl_P256_ecdsa_sign_p256_sha512, Hacl_P256_ecdsa_verif_p256_sha2,
        Hacl_P256_ecdsa_verif_p256_sha384, Hacl_P256_ecdsa_verif_p256_sha512,
    };

    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    pub enum Error {
        InvalidInput,
        SigningError,
    }
    macro_rules! implement {
        ($sign:ident, $fun_sign:expr, $verify:ident, $fun_verify:expr) => {
            /// Sign
            ///
            /// * private key validation must be performed before calling this function
            pub fn $sign(
                payload: &[u8],
                private_key: &[u8; 32],
                nonce: &[u8; 32],
            ) -> Result<[u8; 64], Error> {
                let mut result = [0u8; 64];
                if unsafe {
                    $fun_sign(
                        result.as_mut_ptr(),
                        payload.len().try_into().map_err(|_| Error::InvalidInput)?,
                        payload.as_ptr() as _,
                        private_key.as_ptr() as _,
                        nonce.as_ptr() as _,
                    )
                } {
                    Ok(result)
                } else {
                    Err(Error::SigningError)
                }
            }

            /// Verification
            ///
            /// * public key validation must be performed before calling this function
            pub fn $verify(
                payload: &[u8],
                public_key: &[u8; 64],
                signature_r: &[u8; 32],
                signature_s: &[u8; 32],
            ) -> Result<(), Error> {
                if unsafe {
                    $fun_verify(
                        payload.len().try_into().map_err(|_| Error::InvalidInput)?,
                        payload.as_ptr() as _,
                        public_key.as_ptr() as _,
                        signature_r.as_ptr() as _,
                        signature_s.as_ptr() as _,
                    )
                } {
                    Ok(())
                } else {
                    Err(Error::SigningError)
                }
            }
        };
    }

    implement!(
        sign_sha256,
        Hacl_P256_ecdsa_sign_p256_sha2,
        verify_sha256,
        Hacl_P256_ecdsa_verif_p256_sha2
    );
    implement!(
        sign_sha384,
        Hacl_P256_ecdsa_sign_p256_sha384,
        verify_sha384,
        Hacl_P256_ecdsa_verif_p256_sha384
    );
    implement!(
        sign_sha512,
        Hacl_P256_ecdsa_sign_p256_sha512,
        verify_sha512,
        Hacl_P256_ecdsa_verif_p256_sha512
    );
}
