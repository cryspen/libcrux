use super::impl_hacl::*;

use libcrux_traits::signature::arrayref;

// $bytes is vk_len, sk_len and sig_len
macro_rules! impl_signature_trait {
    ($bits:literal, $bytes:literal, $digest_alg:ident, $alias:ident) => {
        #[allow(non_camel_case_types)]
        // TODO: include in docs that this is an RSA signer?
        #[doc = concat!("A signer using the [`", stringify!($digest_alg),"`] algorithm, ")]
        #[doc = concat!("with a signature length of ", stringify!($bits)," bits ")]
        #[doc = concat!("(", stringify!($bytes)," bytes) ")]
        #[doc = concat!("and a key length of ", stringify!($bits)," bits ")]
        #[doc = concat!("(", stringify!($bytes)," bytes).")]
        pub type $alias = Signer<$bits, $digest_alg>;

        impl arrayref::Sign<(&[u8], &[u8; $bytes]), $bytes, $bytes> for $alias {
            fn sign(
                payload: &[u8],
                signing_key: &[u8; $bytes],
                signature: &mut [u8; $bytes],
                (salt, verification_key): (&[u8], &[u8; $bytes]),
            ) -> Result<(), arrayref::SignError> {
                // NOTE: succeeds if the length of verification_key ($bytes) is 256, 384, 512, 768, 1024
                let pk = VarLenPublicKey::try_from(verification_key.as_ref()).unwrap();
                let sk = VarLenPrivateKey {
                    pk,
                    d: signing_key.as_ref(),
                };
                sign_varlen(
                    crate::DigestAlgorithm::$digest_alg,
                    &sk,
                    payload,
                    salt,
                    signature,
                )
                .map_err(|e| match e {
                    // TODO: is this correct?
                    crate::Error::MessageTooLarge => arrayref::SignError::InvalidPayloadLength,
                    _ => arrayref::SignError::LibraryError,

                })
            }
        }
        impl arrayref::Verify<u32, $bytes, $bytes> for $alias {
            fn verify(
                payload: &[u8],
                verification_key: &[u8; $bytes],
                signature: &[u8; $bytes],
                salt_len: u32,
            ) -> Result<(), arrayref::VerifyError> {
                verify_varlen(
                    crate::DigestAlgorithm::$digest_alg,
                    &VarLenPublicKey::try_from(verification_key.as_ref()).unwrap(),
                    payload,
                    salt_len,
                    signature,
                )
                .map_err(|e| match e {
                    // TODO: is this correct?
                    crate::Error::InvalidSignatureLength => arrayref::VerifyError::InvalidSignature,
                    crate::Error::MessageTooLarge => arrayref::VerifyError::InvalidPayloadLength,
                    _ => arrayref::VerifyError::LibraryError,

                })
            }
        }

        libcrux_traits::impl_signature_slice_trait!($alias => $bytes, $bytes, (&[u8], &[u8; $bytes]), (salt, verification_key));
        libcrux_traits::impl_verify_slice_trait!($alias => $bytes, $bytes,  u32, salt_len);

        // TODO: owned and secrets traits not appearing in docs


    };
}

pub mod signers {
    //! [`libcrux_traits::signature`] APIs.

    pub mod digest_alg {
        //! Structs representing digest algorithms.
        pub struct Sha2_256;
        pub struct Sha2_384;
        pub struct Sha2_512;
    }
    use digest_alg::*;

    /// A convenience struct for signature scheme functionality.
    ///
    /// The valid types for `Alg` are found in [`digest_alg`]. The valid values for `BITS` are
    /// 2048, 3072, 4096, 6144, and 8192.
    pub struct Signer<const BITS: usize, Alg> {
        _phantom_data_alg: core::marker::PhantomData<Alg>,
    }
    use super::*;

    impl_signature_trait!(2048, 256, Sha2_256, Signer_2048_Sha2_256);
    impl_signature_trait!(3072, 384, Sha2_256, Signer_3072_Sha2_256);
    impl_signature_trait!(4096, 512, Sha2_256, Signer_4096_Sha2_256);
    impl_signature_trait!(6144, 768, Sha2_256, Signer_6144_Sha2_256);
    impl_signature_trait!(8192, 1024, Sha2_256, Signer_8192_Sha2_256);

    impl_signature_trait!(2048, 256, Sha2_384, Signer_2048_Sha2_384);
    impl_signature_trait!(3072, 384, Sha2_384, Signer_3072_Sha2_384);
    impl_signature_trait!(4096, 512, Sha2_384, Signer_4096_Sha2_384);
    impl_signature_trait!(6144, 768, Sha2_384, Signer_6144_Sha2_384);
    impl_signature_trait!(8192, 1024, Sha2_384, Signer_8192_Sha2_384);

    impl_signature_trait!(2048, 256, Sha2_512, Signer_2048_Sha2_512);
    impl_signature_trait!(3072, 384, Sha2_512, Signer_3072_Sha2_512);
    impl_signature_trait!(4096, 512, Sha2_512, Signer_4096_Sha2_512);
    impl_signature_trait!(6144, 768, Sha2_512, Signer_6144_Sha2_512);
    impl_signature_trait!(8192, 1024, Sha2_512, Signer_8192_Sha2_512);
}
