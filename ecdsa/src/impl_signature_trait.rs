use libcrux_traits::signature::arrayref;

const SIG_LEN: usize = 64;
const PK_LEN: usize = 64;
const SK_LEN: usize = 32;

macro_rules! impl_signature_trait {
    ($digest_alg_name:ident, $alias:ident, $sign_fn:ident, $verify_fn:ident) => {
        #[allow(non_camel_case_types)]
        pub type $alias = Signer<libcrux_sha2::$digest_alg_name>;

        impl arrayref::Sign<&Nonce, SK_LEN, SIG_LEN> for $alias {
            #[inline(always)]
            fn sign(
                payload: &[u8],
                private_key: &[u8; SK_LEN],
                signature: &mut [u8; SIG_LEN],
                nonce: &Nonce,
            ) -> Result<(), arrayref::SignError> {
                let result = libcrux_p256::$sign_fn(
                    signature,
                    payload.len().try_into().map_err(|_| arrayref::SignError::InvalidPayloadLength)?,
                    payload,
                    private_key,
                    &nonce.0,
                );
                if !result {
                    return Err(arrayref::SignError::LibraryError);
                }
                Ok(())
            }
        }
        impl arrayref::Verify<&(), PK_LEN, SIG_LEN> for $alias {
            #[inline(always)]
            fn verify(
                payload: &[u8],
                public_key: &[u8; PK_LEN],
                signature: &[u8; SIG_LEN],
                _aux: &(),
            ) -> Result<(), arrayref::VerifyError> {

                let result = libcrux_p256::$verify_fn(
                    payload.len().try_into().map_err(|_| arrayref::VerifyError::InvalidPayloadLength)?,
                    payload,
                    public_key,
                    <&[u8; 32]>::try_from(&signature[0..32]).unwrap(),
                    <&[u8; 32]>::try_from(&signature[32..]).unwrap(),
                );
                if !result {
                    return Err(arrayref::VerifyError::LibraryError);
                }
                Ok(())
            }
        }
        libcrux_traits::impl_signature_slice_trait!($alias => SK_LEN, SIG_LEN, &Nonce, nonce);
        libcrux_traits::impl_verify_slice_trait!($alias => PK_LEN, SIG_LEN, &(), _aux);
        // TODO: owned and secrets traits not appearing in docs
    };
}

pub mod p256 {

    use super::*;

    use crate::p256::Nonce;
    pub struct Signer<T> {
        _phantom_data: core::marker::PhantomData<T>,
    }

    impl_signature_trait!(
        Sha256,
        Signer_Sha2_256,
        ecdsa_sign_p256_sha2,
        ecdsa_verif_p256_sha2
    );
    impl_signature_trait!(
        Sha384,
        Signer_Sha2_384,
        ecdsa_sign_p256_sha384,
        ecdsa_verif_p256_sha384
    );
    impl_signature_trait!(
        Sha512,
        Signer_Sha2_512,
        ecdsa_sign_p256_sha512,
        ecdsa_verif_p256_sha512
    );
}
