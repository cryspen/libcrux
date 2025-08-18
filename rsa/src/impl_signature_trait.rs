use super::impl_hacl::*;

use libcrux_secrets::U8;
use libcrux_traits::signature::{arrayref, owned, secrets, slice};

#[cfg(feature = "check-secret-independence")]
impl<'a> libcrux_secrets::Declassify for VarLenPrivateKey<'a, U8> {
    type Declassified = VarLenPrivateKey<'a, u8>;
    fn declassify(self) -> Self::Declassified {
        use libcrux_secrets::DeclassifyRef;
        VarLenPrivateKey {
            pk: self.pk,
            d: self.d.declassify_ref(),
        }
    }
}

// $bytes is vk_len, sk_len and sig_len
macro_rules! impl_signature_trait {
    ($bits:literal, $bytes:literal, $digest_alg:ident, $alias:ident) => {
        #[allow(non_camel_case_types)]
        #[doc = concat!("A signer using the [`", stringify!($digest_alg),"`] algorithm, ")]
        #[doc = concat!("with a signature length of ", stringify!($bits)," bits ")]
        #[doc = concat!("(", stringify!($bytes)," bytes) ")]
        #[doc = concat!("and a key length of ", stringify!($bits)," bits ")]
        #[doc = concat!("(", stringify!($bytes)," bytes).")]
        pub type $alias = Signer<$bits, $digest_alg>;

        /// The [`arrayref`] version of the Sign trait.
        impl arrayref::Sign<$bytes, $bytes> for $alias {

            /// The salt, provided as a `&'a [u8]`.
            type SignAux<'a> = &'a [u8];
            type SigningKey<'a, const LEN: usize> = &'a PrivateKey<LEN, u8>;
            /// Sign a payload using a provided signing key and `salt`.
            fn sign(
                payload: &[u8],
                signing_key: &PrivateKey<$bytes, u8>,
                signature: &mut [u8; $bytes],
                salt: &[u8],
            ) -> Result<(), arrayref::SignError> {
                sign_varlen(
                    crate::DigestAlgorithm::$digest_alg,
                    &signing_key.as_var_len(),
                    payload,
                    salt,
                    signature,
                )
                .map_err(|e| match e {
                    crate::Error::MessageTooLarge => arrayref::SignError::InvalidPayloadLength,
                    _ => arrayref::SignError::LibraryError,

                })
            }
        }
        /// The [`arrayref`] version of the Verify trait.
        impl arrayref::Verify<$bytes, $bytes> for $alias {
            type VerifyAux<'a> = u32;

            /// Verify a signature using a provided verification key and `salt_len`.
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
                    crate::Error::InvalidSignatureLength => arrayref::VerifyError::InvalidSignatureBufferLength,
                    crate::Error::MessageTooLarge => arrayref::VerifyError::InvalidPayloadLength,
                    _ => arrayref::VerifyError::LibraryError,

                })
            }
        }

        // manual implementation of sign slice trait
        /// The [`mod@slice`] version of the Sign trait.
        impl slice::Sign for $alias {

            /// The salt, provided as a `&'a [u8]`.
            type SignAux<'a> = &'a [u8];
            type SigningKey<'a> = VarLenPrivateKey<'a, u8>;
            /// Sign a payload using a provided signing key and `salt`.
            fn sign(
                payload: &[u8],
                signing_key: VarLenPrivateKey<'_, u8>,
                signature: &mut [u8],
                salt: &[u8],
            ) -> Result<(), slice::SignError> {
                sign_varlen(

                    crate::DigestAlgorithm::$digest_alg,
                    &signing_key,
                    payload,
                    salt,
                    signature,
                )
                .map_err(|e| match e {
                    crate::Error::MessageTooLarge => slice::SignError::InvalidPayloadLength,
                    _ => slice::SignError::LibraryError,

                })
            }
        }

        // manual implementation of secrets trait
        /// The [`secrets`] version of the Sign trait, which uses [`libcrux_secrets`] types.
        impl secrets::Sign<$bytes, $bytes> for $alias {
            /// The salt, provided as a `&'a [u8]`.
            type SignAux<'a> = &'a [u8];
            type SigningKey<'a, const LEN: usize> = &'a PrivateKey<$bytes, U8>;

            /// Sign a payload using a provided signing key and `salt`.
            fn sign(
                payload: &[u8],
                signing_key: &PrivateKey<$bytes, U8>,
                salt: &[u8],

            ) -> Result<[u8; $bytes], secrets::SignError> {

                use libcrux_secrets::DeclassifyRef;

                <Self as owned::Sign<_, _>>::sign(payload, signing_key.declassify_ref(), salt)

            }

        }


        libcrux_traits::impl_verify_slice_trait!($alias => $bytes, $bytes,  u32, salt_len);

        // TODO: owned trait not appearing in docs


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
