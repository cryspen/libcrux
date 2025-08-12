use libcrux_traits::signature::arrayref;

macro_rules! impl_signature_trait {
    ($digest_alg_name:ident, $pk_len:literal, $sk_len:literal, $sig_len:literal, $alias:ident, $sign_fn:ident, $verify_fn:ident) => {
        #[allow(non_camel_case_types)]
        pub type $alias = Signer<libcrux_sha2::$digest_alg_name>;

        impl arrayref::Sign<&Nonce, $sk_len, $sig_len> for $alias {
            #[inline(always)]
            fn sign(
                payload: &[u8],
                private_key: &[u8; $sk_len],
                signature: &mut [u8; $sig_len],
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
        impl arrayref::Verify<&(), $pk_len, $sig_len> for $alias {
            #[inline(always)]
            fn verify(
                payload: &[u8],
                public_key: &[u8; $pk_len],
                signature: &[u8; $sig_len],
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
        libcrux_traits::impl_signature_slice_trait!($alias => $sk_len, $sig_len, &Nonce, nonce);
        libcrux_traits::impl_verify_slice_trait!($alias => $pk_len, $sig_len, &(), _aux);
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
        64,
        32,
        64,
        Signer_Sha2_256,
        ecdsa_sign_p256_sha2,
        ecdsa_verif_p256_sha2
    );
    impl_signature_trait!(
        Sha384,
        64,
        32,
        64,
        Signer_Sha2_384,
        ecdsa_sign_p256_sha384,
        ecdsa_verif_p256_sha384
    );
    impl_signature_trait!(
        Sha512,
        64,
        32,
        64,
        Signer_Sha2_512,
        ecdsa_sign_p256_sha512,
        ecdsa_verif_p256_sha512
    );
}
