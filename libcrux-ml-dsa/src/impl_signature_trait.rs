#[cfg(not(eurydice))]
#[cfg_attr(hax, hax_lib::exclude)]
pub mod signers {
    //! [`libcrux_traits::signature`] APIs.
    use libcrux_traits::signature::owned;

    /// A trait representing the context used for ML-DSA signing and verification.
    ///
    /// Can be implemented using the convenience macro [`impl_context`].
    pub trait Context {
        /// Return the context.
        fn context() -> &'static [u8];
    }

    #[macro_export]
    /// A convenience macro for implementing the [`Context`] trait.
    /// The `$context` must be provided as a `&'static [u8]`.
    ///
    /// Usage:
    /// ```rust
    /// use libcrux_ml_dsa::signers::{Context, impl_context};
    /// impl_context!(AppContext, b"context");
    /// ```
    macro_rules! impl_context {
        ($name:ident, $context:literal) => {
            pub struct $name;
            impl Context for $name {
                fn context() -> &'static [u8] {
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
                impl<T: Context>
                    owned::Sign<
                        SIGNING_KEY_LEN,
                        VERIFICATION_KEY_LEN,
                        SIGNATURE_LEN,
                        RAND_KEYGEN_LEN,
                    > for $name<T>
                {
                    /// The `randomness` required for signing.
                    type SignAux<'a> = super::Randomness;

                    /// Sign a payload using a provided signing key, context, and randomness.
                    fn sign(
                        payload: &[u8],
                        signing_key: &[u8; SIGNING_KEY_LEN],
                        randomness: super::Randomness,
                    ) -> Result<[u8; SIGNATURE_LEN], owned::SignError> {
                        crate::ml_dsa_generic::multiplexing::$module::sign(
                            signing_key,
                            payload,
                            T::context(),
                            randomness,
                        )
                        .map(|sig| sig.value)
                        .map_err(|_| owned::SignError::LibraryError)
                    }
                    /// Verify a signature using a provided verification key and context.
                    fn verify(
                        payload: &[u8],
                        verification_key: &[u8; VERIFICATION_KEY_LEN],
                        signature: &[u8; SIGNATURE_LEN],
                    ) -> Result<(), owned::VerifyError> {
                        crate::ml_dsa_generic::multiplexing::$module::verify(
                            verification_key,
                            payload,
                            T::context(),
                            signature,
                        )
                        .map_err(|_| owned::VerifyError::LibraryError)
                    }
                    fn keygen(
                        randomness: Randomness,
                    ) -> Result<
                        ([u8; SIGNING_KEY_LEN], [u8; VERIFICATION_KEY_LEN]),
                        owned::KeyGenError,
                    > {
                        let mut signing_key = [0u8; SIGNING_KEY_LEN];
                        let mut verification_key = [0u8; VERIFICATION_KEY_LEN];
                        crate::ml_dsa_generic::multiplexing::$module::generate_key_pair(
                            randomness,
                            &mut signing_key,
                            &mut verification_key,
                        );

                        Ok((signing_key, verification_key))
                    }
                }
                impl<T: Context> libcrux_traits::signature::key_centric_owned::SignTypes for $name<T> {
                    type SigningKey = [u8; SIGNING_KEY_LEN];
                    type VerificationKey = [u8; VERIFICATION_KEY_LEN];
                    type Signature = [u8; SIGNATURE_LEN];
                    type KeyGenRandomness = [u8; RAND_KEYGEN_LEN];
                    type SignAux<'a> = <$name<T> as libcrux_traits::signature::owned::Sign<
                        SIGNING_KEY_LEN,
                        VERIFICATION_KEY_LEN,
                        SIGNATURE_LEN,
                        RAND_KEYGEN_LEN,
                    >>::SignAux<'a>;
                }

            }
            pub use $module::$name;
        };
    }

    const RAND_KEYGEN_LEN: usize = 32;
    type Randomness = [u8; RAND_KEYGEN_LEN];

    #[cfg(feature = "mldsa44")]
    impl_signature_trait!(ml_dsa_44, MlDsa44Signer);
    #[cfg(feature = "mldsa65")]
    impl_signature_trait!(ml_dsa_65, MlDsa65Signer);
    #[cfg(feature = "mldsa87")]
    impl_signature_trait!(ml_dsa_87, MlDsa87Signer);
}
