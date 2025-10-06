#[cfg(not(eurydice))]
#[cfg_attr(hax, hax_lib::exclude)]
pub mod signers {
    //! [`libcrux_traits::signature`] APIs.

    use libcrux_secrets::{Declassify, DeclassifyRef, DeclassifyRefMut, U8};
    use libcrux_traits::signature::arrayref;

    /// A trait representing the context used for ML-DSA signing and verification.
    ///
    /// Can be implemented using the convenience macro [`impl_context`].
    pub trait Context {
        /// This is a buffer of valid size. The validity trait is private, so the users can't
        /// flag more sizes as valid and circumvent the type safety we established here.
        #[allow(private_bounds)]
        type Buf: ValidContextBuf;

        /// Return the context.
        fn context() -> &'static Self::Buf;
    }

    trait ValidContextBuf {}

    // Implement ValidContextBuf for all sizes 0..=255
    macro_rules! define_valid_buf {
        () => {
            define_valid_buf!(0);
            define_valid_buf!(1);
            define_valid_buf!(2, 0);
            define_valid_buf!(2, 1);
            define_valid_buf!(2, 2);
            define_valid_buf!(2, 3);
            define_valid_buf!(2, 4);
            define_valid_buf!(2, 5, 0);
            define_valid_buf!(2, 5, 1);
            define_valid_buf!(2, 5, 2);
            define_valid_buf!(2, 5, 3);
            define_valid_buf!(2, 5, 4);
            define_valid_buf!(2, 5, 5);
        };
        ($num:expr) => {
            define_valid_buf!($num, 0);
            define_valid_buf!($num, 1);
            define_valid_buf!($num, 2);
            define_valid_buf!($num, 3);
            define_valid_buf!($num, 4);
            define_valid_buf!($num, 5);
            define_valid_buf!($num, 6);
            define_valid_buf!($num, 7);
            define_valid_buf!($num, 8);
            define_valid_buf!($num, 9);
        };
        ($num1:expr,$num2:expr) => {
            define_valid_buf!($num1, $num2, 0);
            define_valid_buf!($num1, $num2, 1);
            define_valid_buf!($num1, $num2, 2);
            define_valid_buf!($num1, $num2, 3);
            define_valid_buf!($num1, $num2, 4);
            define_valid_buf!($num1, $num2, 5);
            define_valid_buf!($num1, $num2, 6);
            define_valid_buf!($num1, $num2, 7);
            define_valid_buf!($num1, $num2, 8);
            define_valid_buf!($num1, $num2, 9);
        };
        ($num1:expr,$num2:expr,$num3:expr) => {
            impl ValidContextBuf for [u8; $num1 * 100 + $num2 * 10 + $num3] {}
        };
    }

    define_valid_buf!();

    #[macro_export]
    /// A convenience macro for implementing the [`Context`] trait.
    /// The `$context` must be provided as a `&'static [u8; $len]`.
    ///
    /// Usage:
    /// ```rust
    /// use libcrux_ml_dsa::signers::{Context, impl_context};
    /// impl_context!(AppContext, b"context", 7);
    /// ```
    macro_rules! impl_context {
        ($name:ident, $context:literal,$len:expr) => {
            impl_context!(
                $name,
                $context,
                $len,
                concat!(
                    "An ML-DSA signing context that contains \"",
                    stringify!($context),
                    "\"."
                )
            )
        };
        ($name:ident, $context:literal, $len:expr, $doc:expr) => {
            #[doc = $doc]
            pub struct $name;
            impl Context for $name {
                type Buf = [u8; $len];
                fn context() -> &'static [u8; $len] {
                    $context
                }
            }
        };
    }
    pub use impl_context;

    macro_rules! impl_signature_trait {
        ($module:ident, $name:tt) => {
            mod $module {
                use super::*;

                #[doc = concat!("An ", stringify!($module), " signer.\n\n")]
                /// The `context` can be defined using the [`Context`] trait.
                pub struct $name<T: Context> {
                    _context: core::marker::PhantomData<T>,
                }

                const VERIFICATION_KEY_LEN: usize =
                    crate::ml_dsa_generic::$module::VERIFICATION_KEY_SIZE;
                const SIGNING_KEY_LEN: usize = crate::ml_dsa_generic::$module::SIGNING_KEY_SIZE;
                const SIGNATURE_LEN: usize = crate::ml_dsa_generic::$module::SIGNATURE_SIZE;

                // NOTE: implementing owned trait directly because there is no arrayref equivalent
                /// The [`owned`](libcrux_traits::signature::owned) version of the Sign trait.
                ///
                /// It is the responsibility of the caller to ensure  that the `randomness` argument is actually
                /// random.
                impl<const N: usize, T: Context<Buf = [u8; N]>>
                    arrayref::Sign<
                        SIGNING_KEY_LEN,
                        VERIFICATION_KEY_LEN,
                        SIGNATURE_LEN,
                        RAND_KEYGEN_LEN,
                    > for $name<T>
                {
                    /// Sign a payload using a provided signing key, context, and randomness.
                    fn sign(
                        payload: &[u8],
                        signing_key: &[U8; SIGNING_KEY_LEN],
                        signature: &mut [u8; SIGNATURE_LEN],
                        randomness: super::Randomness,
                    ) -> Result<(), arrayref::SignError> {
                        crate::ml_dsa_generic::multiplexing::$module::sign_mut(
                            signing_key.declassify_ref(),
                            payload,
                            T::context(),
                            randomness.declassify(),
                            signature,
                        )
                        .map_err(|err| {
                            use crate::types::SigningError::*;
                            match err {
                                RejectionSamplingError => arrayref::SignError::InvalidRandomness,
                                ContextTooLongError => arrayref::SignError::InvalidArgument,
                            }
                        })
                    }
                    /// Verify a signature using a provided verification key and context.
                    fn verify(
                        payload: &[u8],
                        verification_key: &[u8; VERIFICATION_KEY_LEN],
                        signature: &[u8; SIGNATURE_LEN],
                    ) -> Result<(), arrayref::VerifyError> {
                        crate::ml_dsa_generic::multiplexing::$module::verify(
                            verification_key,
                            payload,
                            T::context(),
                            signature,
                        )
                        .map_err(|err| {
                            use crate::types::VerificationError::*;

                            match err {
                                MalformedHintError
                                | SignerResponseExceedsBoundError
                                | CommitmentHashesDontMatchError => {
                                    arrayref::VerifyError::InvalidSignature
                                }
                                VerificationContextTooLongError => arrayref::VerifyError::LibraryError,
                            }
                        })
                    }

                    fn keygen_derand(
                        signing_key: &mut [U8; SIGNING_KEY_LEN],
                        verification_key: &mut [u8; VERIFICATION_KEY_LEN],
                        randomness: &Randomness,
                    ) -> Result<(), arrayref::KeyGenError> {
                        crate::ml_dsa_generic::multiplexing::$module::generate_key_pair(
                            (*randomness).declassify(),
                            signing_key.declassify_ref_mut(),
                            verification_key,
                        );

                        Ok(())
                    }
                }
                impl<T: Context> libcrux_traits::signature::key_centric_owned::SignTypes for $name<T> {
                    type SigningKey = [U8; SIGNING_KEY_LEN];
                    type VerificationKey = [u8; VERIFICATION_KEY_LEN];
                    type Signature = [u8; SIGNATURE_LEN];
                    type KeyGenRandomness = [U8; RAND_KEYGEN_LEN];
                    /// The `randomness` required for signing.
                    type SignAux<'a> = super::Randomness;
                }
            }
            pub use $module::$name;
        };
    }

    const RAND_KEYGEN_LEN: usize = 32;
    type Randomness = [U8; RAND_KEYGEN_LEN];

    #[cfg(feature = "mldsa44")]
    impl_signature_trait!(ml_dsa_44, MlDsa44Signer);
    #[cfg(feature = "mldsa65")]
    impl_signature_trait!(ml_dsa_65, MlDsa65Signer);
    #[cfg(feature = "mldsa87")]
    impl_signature_trait!(ml_dsa_87, MlDsa87Signer);
}
