use libcrux_traits::signature::{arrayref, owned};

impl From<crate::SigningError> for owned::SignError {
    fn from(e: crate::SigningError) -> Self {
        match e {
            crate::SigningError::RejectionSamplingError => todo!(),
            crate::SigningError::ContextTooLongError => todo!(),
        }
    }
}
impl From<crate::VerificationError> for arrayref::VerifyError {
    fn from(e: crate::VerificationError) -> Self {
        match e {
            crate::VerificationError::MalformedHintError => todo!(),
            crate::VerificationError::SignerResponseExceedsBoundError => todo!(),
            crate::VerificationError::CommitmentHashesDontMatchError => todo!(),
            crate::VerificationError::VerificationContextTooLongError => todo!(),
        }
    }
}

macro_rules! impl_signature_trait {
    ($name:ident, $module:ident, $alias:ident, $doc:expr) => {
        mod $module {
            use libcrux_traits::signature::{arrayref, owned};
            #[doc = $doc]
            pub struct $name;

            pub type $alias = super::Signer<$name>;

            const VERIFICATION_KEY_LEN: usize =
                crate::ml_dsa_generic::$module::VERIFICATION_KEY_SIZE;
            const SIGNING_KEY_LEN: usize = crate::ml_dsa_generic::$module::SIGNING_KEY_SIZE;
            const SIGNATURE_LEN: usize = crate::ml_dsa_generic::$module::SIGNATURE_SIZE;

            // XXX: implementing owned trait directly because there is no arrayref equivalent
            // TODO: for docs, these should appear as consts in trait def
            impl owned::SignWithAux<super::Randomness, SIGNING_KEY_LEN, SIGNATURE_LEN> for $alias {
                fn sign(
                    payload: &[u8],
                    private_key: &[u8; SIGNING_KEY_LEN],
                    randomness: super::Randomness,
                ) -> Result<[u8; SIGNATURE_LEN], owned::SignError> {
                    crate::ml_dsa_generic::multiplexing::$module::sign(
                        private_key,
                        payload,
                        &[],
                        randomness,
                    )
                    .map(|sig| sig.value)
                    .map_err(owned::SignError::from)
                }
            }
            impl arrayref::VerifyWithAux<&(), VERIFICATION_KEY_LEN, SIGNATURE_LEN> for $alias {
                fn verify(
                    payload: &[u8],
                    public_key: &[u8; VERIFICATION_KEY_LEN],
                    signature: &[u8; SIGNATURE_LEN],
                    _aux: &(),
                ) -> Result<(), owned::VerifyError> {
                    crate::ml_dsa_generic::multiplexing::$module::verify(
                        public_key,
                        payload,
                        &[],
                        signature,
                    )
                    .map_err(arrayref::VerifyError::from)
                }
            }

            // TODO: secrets trait not appearing in docs
        }
        pub use $module::{$alias, $name};
    };
}
pub struct Signer<T> {
    _phantom_data: core::marker::PhantomData<T>,
}

type Randomness = [u8; 32];

impl_signature_trait!(
    MlDsa44,
    ml_dsa_44,
    MlDsa44Signer,
    "A struct representing ML-DSA 44"
);
impl_signature_trait!(
    MlDsa65,
    ml_dsa_65,
    MlDsa65Signer,
    "A struct representing ML-DSA 65"
);
impl_signature_trait!(
    MlDsa87,
    ml_dsa_87,
    MlDsa87Signer,
    "A struct representing ML-DSA 87"
);
