use super::impl_hacl::*;

use libcrux_secrets::{DeclassifyRef, U8};
use libcrux_traits::signature::{arrayref, owned, secrets, slice};

/// An RSA Public Key that is `LEN` bytes long, backed by array references.
#[derive(Debug, Clone)]
pub struct PublicKeyBorrow<'a, const LEN: usize> {
    n: &'a [u8; LEN],
}

/// An RSA Private Key that is `LEN` bytes long, backed by array references.
pub struct PrivateKeyBorrow<'a, const LEN: usize> {
    pk: PublicKeyBorrow<'a, LEN>,
    d: &'a [u8; LEN],
}

/// An RSA Private Key that is `LEN` bytes long, backed by array references.
/// the private key is represented using [`type@libcrux_secrets::U8`], as a `&'a [U8; LEN]`.
pub struct PrivateKeyBorrowClassified<'a, const LEN: usize> {
    pk: PublicKeyBorrow<'a, LEN>,
    d: &'a [U8; LEN],
}

impl<'a, const LEN: usize> PrivateKeyBorrowClassified<'a, LEN> {
    /// Constructor for the private key based on `n` and `d`.
    pub fn from_components(n: &'a [u8; LEN], d: &'a [U8; LEN]) -> Self {
        Self {
            pk: PublicKeyBorrow { n },
            d,
        }
    }
}
impl<'a, const LEN: usize> alloc::fmt::Debug for PrivateKeyBorrowClassified<'a, LEN> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("PrivateKey")
            .field("pk", &self.pk)
            .field("d", &"****")
            .finish()
    }
}

impl<'a, const LEN: usize> alloc::fmt::Debug for PrivateKeyBorrow<'a, LEN> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("PrivateKey")
            .field("pk", &self.pk)
            .field("d", &"****")
            .finish()
    }
}

// TODO: `From` trait, or different method?
// TODO: implement these only as certain key lengths?
impl<'a, const LEN: usize> From<&'a PublicKey<LEN>> for PublicKeyBorrow<'a, LEN> {
    #[inline(always)]
    fn from(pk: &'a PublicKey<LEN>) -> PublicKeyBorrow<'a, LEN> {
        PublicKeyBorrow { n: &pk.n }
    }
}
impl<'a, const LEN: usize> From<&'a PrivateKey<LEN>> for PrivateKeyBorrow<'a, LEN> {
    #[inline(always)]
    fn from(sk: &'a PrivateKey<LEN>) -> PrivateKeyBorrow<'a, LEN> {
        PrivateKeyBorrow {
            pk: (&sk.pk).into(),
            d: &sk.d,
        }
    }
}
impl<'a, const LEN: usize> PublicKeyBorrow<'a, LEN> {
    #[inline(always)]
    /// Returns the slice-based public key
    pub fn as_var_len(&'a self) -> VarLenPublicKey<'a> {
        VarLenPublicKey { n: self.n.as_ref() }
    }
}

impl<'a, const LEN: usize> PrivateKeyBorrow<'a, LEN> {
    #[inline(always)]
    /// Returns the slice-based private key
    pub fn as_var_len(&'a self) -> VarLenPrivateKey<'a> {
        VarLenPrivateKey {
            pk: self.pk.as_var_len(),
            d: self.d.as_ref(),
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

        impl arrayref::Sign<$bytes, $bytes> for $alias {

            type SignAux<'a> = &'a [u8];
            type SigningKey<'a, const LEN: usize> = PrivateKeyBorrow<'a, LEN>;
            fn sign(
                payload: &[u8],
                signing_key: PrivateKeyBorrow<'_, $bytes>,
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
        impl arrayref::Verify<$bytes, $bytes> for $alias {
            type VerifyAux<'a> = u32;

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
        impl slice::Sign for $alias {

            type SignAux<'a> = &'a [u8];
            type SigningKey<'a> = VarLenPrivateKey<'a>;
            fn sign(
                payload: &[u8],
                signing_key: VarLenPrivateKey<'_>,
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
        impl secrets::Sign<$bytes, $bytes> for $alias {
            type SignAux<'a> = &'a [u8];
            type SigningKey<'a, const LEN: usize> = PrivateKeyBorrowClassified<'a, $bytes>;

            fn sign(
                payload: &[u8],
                signing_key: PrivateKeyBorrowClassified<'_, $bytes>,
                salt: &[u8],

            ) -> Result<[u8; $bytes], secrets::SignError> {

                // XXX: This transformation is not done by implementing
                // `libcrux_secrets::Classify` for the key, because the implementation would conflict
                // with the existing `impl<T> Classify for T` in
                // libcrux_secrets::int::public_integers.
                let declassified = PrivateKeyBorrow {
                    pk: signing_key.pk,
                    d: signing_key.d.declassify_ref(),
                };

                <Self as owned::Sign<$bytes, $bytes>>::sign(payload, declassified, salt)
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
