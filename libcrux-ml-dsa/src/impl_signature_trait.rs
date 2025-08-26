#[cfg_attr(hax, hax_lib::exclude)]
pub mod signers {
    //! [`libcrux_traits::signature`] APIs.
    use libcrux_traits::signature::owned;

    macro_rules! impl_signature_trait {
        ($name:ident, $module:ident, $alias:ident, $doc:expr) => {
            mod $module {
                use super::*;

                #[doc = $doc]
                pub struct $name;

                #[doc = concat!("An ", stringify!($module), " signer.")]
                pub type $alias = super::Signer<$name>;

                const VERIFICATION_KEY_LEN: usize =
                    crate::ml_dsa_generic::$module::VERIFICATION_KEY_SIZE;
                const SIGNING_KEY_LEN: usize = crate::ml_dsa_generic::$module::SIGNING_KEY_SIZE;
                const SIGNATURE_LEN: usize = crate::ml_dsa_generic::$module::SIGNATURE_SIZE;

                // NOTE: implementing owned trait directly because there is no arrayref equivalent
                /// The [`owned`](libcrux_traits::signature::owned) version of the Sign trait.
                ///
                /// It is the responsibility of the caller to ensure  that the `randomness` argument is actually
                /// random.
                impl owned::Sign<SIGNING_KEY_LEN, VERIFICATION_KEY_LEN, SIGNATURE_LEN> for $alias {
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
                            &[],
                            randomness,
                        )
                        .map(|sig| sig.value)
                        .map_err(|_| owned::SignError::LibraryError)
                    }
                    type VerifyAux<'a> = ();

                    /// Verify a signature using a provided verification key and context.
                    fn verify(
                        payload: &[u8],
                        verification_key: &[u8; VERIFICATION_KEY_LEN],
                        signature: &[u8; SIGNATURE_LEN],
                        _aux: (),
                    ) -> Result<(), owned::VerifyError> {
                        crate::ml_dsa_generic::multiplexing::$module::verify(
                            verification_key,
                            payload,
                            &[],
                            signature,
                        )
                        .map_err(|_| owned::VerifyError::LibraryError)
                    }
                }
            }
            pub use $module::{$alias, $name};
        };
    }

    // List structs in doc comment if enabled.
    /// A convenience struct for signature scheme functionality.
    #[cfg_attr(feature = "mldsa44", doc = "\n - [`MlDsa44`]")]
    #[cfg_attr(feature = "mldsa65", doc = "\n - [`MlDsa65`]")]
    #[cfg_attr(feature = "mldsa87", doc = "\n - [`MlDsa87`]")]
    pub struct Signer<Implementation> {
        _phantom_data: core::marker::PhantomData<Implementation>,
    }

    type Randomness = [u8; 32];

    #[cfg(feature = "mldsa44")]
    impl_signature_trait!(
        MlDsa44,
        ml_dsa_44,
        MlDsa44Signer,
        "A struct representing ML-DSA 44."
    );
    #[cfg(feature = "mldsa65")]
    impl_signature_trait!(
        MlDsa65,
        ml_dsa_65,
        MlDsa65Signer,
        "A struct representing ML-DSA 65."
    );
    #[cfg(feature = "mldsa87")]
    impl_signature_trait!(
        MlDsa87,
        ml_dsa_87,
        MlDsa87Signer,
        "A struct representing ML-DSA 87."
    );
}
