#[cfg_attr(hax, hax_lib::exclude)]
pub mod signers {
    //! [`libcrux_traits::signature`] APIs.
    use libcrux_traits::signature::{arrayref, owned};

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

                // XXX: implementing owned trait directly because there is no arrayref equivalent
                /// It is the responsibility of the caller to ensure  that the `randomness` argument is actually
                /// random.
                impl owned::Sign<(&[u8], super::Randomness), SIGNING_KEY_LEN, SIGNATURE_LEN>
                    for $alias
                {
                    fn sign(
                        payload: &[u8],
                        signing_key: &[u8; SIGNING_KEY_LEN],
                        (context, randomness): (&[u8], super::Randomness),
                    ) -> Result<[u8; SIGNATURE_LEN], owned::SignError> {
                        crate::ml_dsa_generic::multiplexing::$module::sign(
                            signing_key,
                            payload,
                            context,
                            randomness,
                        )
                        .map(|sig| sig.value)
                        .map_err(|_| owned::SignError::LibraryError)
                    }
                }
                impl arrayref::Verify<&[u8], VERIFICATION_KEY_LEN, SIGNATURE_LEN> for $alias {
                    fn verify(
                        payload: &[u8],
                        verification_key: &[u8; VERIFICATION_KEY_LEN],
                        signature: &[u8; SIGNATURE_LEN],
                        context: &[u8],
                    ) -> Result<(), arrayref::VerifyError> {
                        crate::ml_dsa_generic::multiplexing::$module::verify(
                            verification_key,
                            payload,
                            context,
                            signature,
                        )
                        .map_err(|_| arrayref::VerifyError::LibraryError)
                    }
                }

                // TODO: secrets trait not appearing in docs
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
