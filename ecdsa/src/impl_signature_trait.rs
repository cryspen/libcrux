macro_rules! impl_signature_trait {
    ($digest_alg_name:ident, $pk_len:literal, $sk_len:literal, $sig_len:literal) => {
        pub struct $digest_alg_name;

        impl arrayref::Signature<&Nonce, $pk_len, $sk_len, $sig_len> for Signer<$digest_alg_name> {
            fn sign(
                payload: &[u8],
                private_key: &[u8; $sk_len],
                signature: &mut [u8; $sig_len],
                nonce: &Nonce,
            ) -> Result<(), arrayref::SignError> {
                crate::p256::_sign_internal(
                    crate::DigestAlgorithm::$digest_alg_name,
                    payload,
                    private_key,
                    nonce,
                    signature,
                )
                .map_err(|_| todo!())
            }
            fn verify(
                payload: &[u8],
                public_key: &[u8; $pk_len],
                signature: &[u8; $sig_len],
            ) -> Result<(), arrayref::VerifyError> {

                crate::p256::_verify_internal(
                    crate::DigestAlgorithm::$digest_alg_name,
                    payload,
                    <&[u8; 32]>::try_from(&signature[0..32]).unwrap(),
                    <&[u8; 32]>::try_from(&signature[32..]).unwrap(),
                    public_key,
                )
                .map_err(|_| todo!())
            }
        }
        libcrux_traits::impl_signature_slice_trait!(Signer<$digest_alg_name> => $pk_len, $sk_len, $sig_len, &Nonce, nonce);
    };
}

pub mod p256 {

    use crate::p256::Nonce;
    use libcrux_traits::signature::arrayref;
    pub struct Signer<T> {
        _phantom_data: core::marker::PhantomData<T>,
    }

    impl_signature_trait!(Sha256, 64, 32, 64);
    impl_signature_trait!(Sha384, 64, 32, 64);
    impl_signature_trait!(Sha512, 64, 32, 64);
}
