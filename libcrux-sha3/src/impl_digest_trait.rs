use crate::*;

macro_rules! impl_hash_traits {
    ($type:ident, $hasher:ident, $len:expr, $method:expr) => {
        /// TODO: doc comment
        pub struct $type;

        impl libcrux_traits::digest::arrayref::Hash<$len> for $type {
            #[inline(always)]
            fn hash(
                digest: &mut [u8; $len],
                payload: &[u8],
            ) -> Result<(), libcrux_traits::digest::arrayref::HashError> {
                // TODO: return error
                debug_assert!(payload.len() <= u32::MAX as usize);

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
