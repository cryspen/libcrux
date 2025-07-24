use super::impl_hacl::*;

use libcrux_traits::signature::arrayref;

// $bytes is pk_len, sk_len and sig_len
macro_rules! impl_signature_trait {
    ($name:ident, $bytes:literal, $digest_alg:ident) => {
        pub struct $name;

        impl arrayref::Signature<&[u8], $bytes, $bytes, $bytes> for Signer<$name, $digest_alg> {
            fn sign(
                payload: &[u8],
                private_key: &[u8; $bytes],
                signature: &mut [u8; $bytes],
                salt: &[u8],
            ) -> Result<(), arrayref::SignError> {
                sign_varlen(
                    crate::DigestAlgorithm::$digest_alg,
                    todo!("need the private key with the public key here"),
                    payload,
                    salt,
                    signature,
                )
                .map_err(|e| todo!())
            }
            fn verify(
                payload: &[u8],
                public_key: &[u8; $bytes],
                signature: &[u8; $bytes],
            ) -> Result<(), arrayref::VerifyError> {
                verify_varlen(
                    crate::DigestAlgorithm::$digest_alg,
                    &VarLenPublicKey::try_from(public_key.as_ref()).unwrap(),
                    payload,
                    todo!("need the salt length here"),
                    signature,
                )
                .map_err(|e| todo!())
            }
        }
    };
}

pub struct Sha2_256;
pub struct Sha2_384;
pub struct Sha2_512;

pub struct Signer<Bits, Alg> {
    _phantom_data_bits: core::marker::PhantomData<Bits>,
    _phantom_data_alg: core::marker::PhantomData<Alg>,
}
impl_signature_trait!(Bits2048, 256, Sha2_256);
impl_signature_trait!(Bits3072, 384, Sha2_256);
impl_signature_trait!(Bits4096, 512, Sha2_256);
impl_signature_trait!(Bits6144, 768, Sha2_256);
impl_signature_trait!(Bits8192, 1024, Sha2_256);
