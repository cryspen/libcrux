use libcrux_traits::digest::{DigestIncrementalBase, InitializeDigestState, UpdateError};

use crate::{generic_keccak::xof::KeccakXofState, *};

const SHA3_224_LEN: usize = 28;
const SHA3_256_LEN: usize = 32;
const SHA3_384_LEN: usize = 48;
const SHA3_512_LEN: usize = 64;

macro_rules! impl_hash_traits {
    ($type:ident, $hasher:ident, $len:expr, $rate:expr, $method:expr) => {
        /// A struct that implements [`libcrux_traits::digest`] traits.
        pub struct $type {
            state: KeccakXofState<1, $rate, u64>,
        }

        impl InitializeDigestState for $type {
            fn new() -> Self {
                Self {
                    state: KeccakXofState::<1, $rate, u64>::new(),
                }
            }
        }

        impl DigestIncrementalBase for $type {
            type IncrementalState = Self;

            fn reset(state: &mut Self::IncrementalState) {
                *state = Self::IncrementalState::new();
            }

            fn update(
                state: &mut Self::IncrementalState,
                payload: &[u8],
            ) -> Result<(), UpdateError> {
                state.state.absorb(&[payload]);
                Ok(())
            }
        }
        #[doc = concat!("A hasher for [`",stringify!($type), "`].")]
        pub type $hasher = libcrux_traits::digest::Hasher<$len, $type>;

        // Squeeze is only implemented for the correct digest lengths.
        impl libcrux_traits::digest::arrayref::DigestIncremental<$len> for $type {
            fn finish(mut state: Self::IncrementalState, digest: &mut [u8; $len]) {
                state.state.absorb_final::<0x06u8>(&[&[]]);
                state.state.squeeze(digest);
            }
        }

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

impl_hash_traits!(
    Sha3_224,
    Sha3_224Hasher,
    SHA3_224_LEN,
    144,
    portable::sha224
);
impl_hash_traits!(
    Sha3_256,
    Sha3_256Hasher,
    SHA3_256_LEN,
    136,
    portable::sha256
);
impl_hash_traits!(
    Sha3_384,
    Sha3_384Hasher,
    SHA3_384_LEN,
    104,
    portable::sha384
);
impl_hash_traits!(Sha3_512, Sha3_512Hasher, SHA3_512_LEN, 72, portable::sha512);

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
