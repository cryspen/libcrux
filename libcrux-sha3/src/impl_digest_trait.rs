use crate::*;
pub(crate) const SHA3_224_LEN: usize = 28;
pub(crate) const SHA3_256_LEN: usize = 32;
pub(crate) const SHA3_384_LEN: usize = 48;
pub(crate) const SHA3_512_LEN: usize = 64;

macro_rules! impl_hash_traits {
    ($type:ident, $hasher:ident, $len:expr, $method:expr) => {
        #[doc = concat!("A struct that implements [`libcrux_traits::digest`] traits.")]
        #[doc = concat!("\n\n")]
        #[doc = concat!("[`",stringify!($hasher), "`] is a convenient hasher for this struct.")]
        pub struct $type;

        #[doc = concat!("A hasher for [`",stringify!($type), "`].")]
        pub type $hasher = libcrux_traits::digest::Hasher<$len, $type>;

        impl libcrux_traits::digest::arrayref::Hash<$len> for $type {
            #[inline(always)]
            fn hash(
                digest: &mut [u8; $len],
                payload: &[u8],
            ) -> Result<(), libcrux_traits::digest::arrayref::HashError> {
                if payload.len() > u32::MAX as usize {
                    return Err(libcrux_traits::digest::arrayref::HashError::InvalidPayloadLength);
                }

                $method(digest, payload);

                Ok(())
            }
        }
    };
}

impl_hash_traits!(Sha3_224, Sha3_224Hasher, SHA3_224_LEN, portable::sha224);
impl_hash_traits!(Sha3_256, Sha3_256Hasher, SHA3_256_LEN, portable::sha256);
impl_hash_traits!(Sha3_384, Sha3_384Hasher, SHA3_384_LEN, portable::sha384);
impl_hash_traits!(Sha3_512, Sha3_512Hasher, SHA3_512_LEN, portable::sha512);

// Implement the slice hash trait
// This is excluded for the hax extraction
#[cfg_attr(hax, hax_lib::exclude)]
mod slice {
    use super::*;

    libcrux_traits::digest::slice::impl_hash_trait!(Sha3_224 => SHA3_224_LEN);
    libcrux_traits::digest::slice::impl_hash_trait!(Sha3_256 => SHA3_256_LEN);
    libcrux_traits::digest::slice::impl_hash_trait!(Sha3_384 => SHA3_384_LEN);
    libcrux_traits::digest::slice::impl_hash_trait!(Sha3_512 => SHA3_512_LEN);
}
