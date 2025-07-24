use super::impl_hacl::*;

use libcrux_traits::signature::arrayref;

// $bytes is pk_len, sk_len and sig_len
macro_rules! impl_signature_trait {
    ($name:ident, $bytes:literal, $digest_alg:ident, $alias:ident) => {
        #[allow(non_camel_case_types)]
        pub type $alias = Signer<$name, $digest_alg>;

        impl arrayref::SignWithAux<(&[u8], &[u8; $bytes]), $bytes, $bytes> for $alias {
            fn sign(
                payload: &[u8],
                private_key: &[u8; $bytes],
                signature: &mut [u8; $bytes],
                (salt, public_key): (&[u8], &[u8; $bytes]),
            ) -> Result<(), arrayref::SignError> {
                // NOTE: succeeds if the length of public_key ($bytes) is 256, 384, 512, 768, 1024
                let pk = VarLenPublicKey::try_from(public_key.as_ref()).unwrap();
                let sk = VarLenPrivateKey {
                    pk,
                    d: private_key.as_ref(),
                };
                sign_varlen(
                    crate::DigestAlgorithm::$digest_alg,
                    &sk,
                    payload,
                    salt,
                    signature,
                )
                .map_err(|_| todo!())
            }
        }
        impl arrayref::VerifyWithAux<u32, $bytes, $bytes> for $alias {
            fn verify(
                payload: &[u8],
                public_key: &[u8; $bytes],
                signature: &[u8; $bytes],
                salt_len: u32,
            ) -> Result<(), arrayref::VerifyError> {
                verify_varlen(
                    crate::DigestAlgorithm::$digest_alg,
                    &VarLenPublicKey::try_from(public_key.as_ref()).unwrap(),
                    payload,
                    salt_len,
                    signature,
                )
                .map_err(|_| todo!())
            }
        }

        libcrux_traits::impl_signature_slice_trait!($alias => $bytes, $bytes, (&[u8], &[u8; $bytes]), (salt, public_key));
        libcrux_traits::impl_verify_slice_trait!($alias => $bytes, $bytes,  u32, salt_len);

        // TODO: owned and secrets traits not appearing in docs


    };
}

pub mod pss_bits {
    pub struct Bits2048;
    pub struct Bits3072;
    pub struct Bits4096;
    pub struct Bits6144;
    pub struct Bits8192;
}
use pss_bits::*;

pub mod digest_alg {
    pub struct Sha2_256;
    pub struct Sha2_384;
    pub struct Sha2_512;
}
use digest_alg::*;

pub struct Signer<Bits, Alg> {
    _phantom_data_bits: core::marker::PhantomData<Bits>,
    _phantom_data_alg: core::marker::PhantomData<Alg>,
}
impl_signature_trait!(Bits2048, 256, Sha2_256, Signer_2048_Sha2_256);
impl_signature_trait!(Bits3072, 384, Sha2_256, Signer_3072_Sha2_256);
impl_signature_trait!(Bits4096, 512, Sha2_256, Signer_4096_Sha2_256);
impl_signature_trait!(Bits6144, 768, Sha2_256, Signer_6144_Sha2_256);
impl_signature_trait!(Bits8192, 1024, Sha2_256, Signer_8192_Sha2_256);

impl_signature_trait!(Bits2048, 256, Sha2_384, Signer_2048_Sha2_384);
impl_signature_trait!(Bits3072, 384, Sha2_384, Signer_3072_Sha2_384);
impl_signature_trait!(Bits4096, 512, Sha2_384, Signer_4096_Sha2_384);
impl_signature_trait!(Bits6144, 768, Sha2_384, Signer_6144_Sha2_384);
impl_signature_trait!(Bits8192, 1024, Sha2_384, Signer_8192_Sha2_384);

impl_signature_trait!(Bits2048, 256, Sha2_512, Signer_2048_Sha2_512);
impl_signature_trait!(Bits3072, 384, Sha2_512, Signer_3072_Sha2_512);
impl_signature_trait!(Bits4096, 512, Sha2_512, Signer_4096_Sha2_512);
impl_signature_trait!(Bits6144, 768, Sha2_512, Signer_6144_Sha2_512);
impl_signature_trait!(Bits8192, 1024, Sha2_512, Signer_8192_Sha2_512);
