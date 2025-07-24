use super::impl_hacl::*;

use libcrux_traits::signature::arrayref;

// $bytes is pk_len, sk_len and sig_len
macro_rules! impl_signature_trait {
    ($name:ident, $bytes:literal, $digest_alg:ident) => {
        impl arrayref::Signature<(&[u8], &[u8; $bytes]), u32, $bytes, $bytes, $bytes>
            for Signer<$name, $digest_alg>
        {
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
impl_signature_trait!(Bits2048, 256, Sha2_256);
impl_signature_trait!(Bits3072, 384, Sha2_256);
impl_signature_trait!(Bits4096, 512, Sha2_256);
impl_signature_trait!(Bits6144, 768, Sha2_256);
impl_signature_trait!(Bits8192, 1024, Sha2_256);

impl_signature_trait!(Bits2048, 256, Sha2_384);
impl_signature_trait!(Bits3072, 384, Sha2_384);
impl_signature_trait!(Bits4096, 512, Sha2_384);
impl_signature_trait!(Bits6144, 768, Sha2_384);
impl_signature_trait!(Bits8192, 1024, Sha2_384);

impl_signature_trait!(Bits2048, 256, Sha2_512);
impl_signature_trait!(Bits3072, 384, Sha2_512);
impl_signature_trait!(Bits4096, 512, Sha2_512);
impl_signature_trait!(Bits6144, 768, Sha2_512);
impl_signature_trait!(Bits8192, 1024, Sha2_512);
