//! AES-GCM 128

use crate::{
    aes::AES_BLOCK_LEN,
    aes_gcm::aesgcm,
    ctr::Aes128CtrContext,
    gf128::GF128State,
    platform::{AESState, GF128FieldElement},
    DecryptError, NONCE_LEN, TAG_LEN,
};

// NOTE: hidden here in favor of being re-exported at crate root
#[doc(hidden)]
/// AES-GCM 128 key length.
pub const KEY_LEN: usize = 16;
pub(crate) const GCM_KEY_LEN: usize = 16;

/// The AES-GCM 128 state
pub(crate) struct State<T: AESState, U: GF128FieldElement> {
    pub(crate) aes_state: Aes128CtrContext<T>,
    pub(crate) gcm_state: GF128State<U>,
    pub(crate) tag_mix: [u8; TAG_LEN],
}

aesgcm!(State<T, U>, Aes128CtrContext);

macro_rules! platform_mod {
    ($implementation:ident) => {
        pub use crate::implementations::$implementation;
        #[doc = concat!("An owned ",stringify!($implementation), " key.")]
        pub type Key = libcrux_traits::aead::typed_owned::Key<$implementation>;
        #[doc = concat!("An owned ",stringify!($implementation), " tag.")]
        pub type Tag = libcrux_traits::aead::typed_owned::Tag<$implementation>;
        #[doc = concat!("An owned ",stringify!($implementation), " nonce.")]
        pub type Nonce = libcrux_traits::aead::typed_owned::Nonce<$implementation>;
        #[doc = concat!("A reference to a ",stringify!($implementation), " key.")]
        pub type KeyRef<'a> = libcrux_traits::aead::typed_refs::KeyRef<'a, $implementation>;
        #[doc = concat!("A reference to a ",stringify!($implementation), " tag.")]
        pub type TagRef<'a> = libcrux_traits::aead::typed_refs::TagRef<'a, $implementation>;
        #[doc = concat!("A mutable reference to a ",stringify!($implementation), " tag.")]
        pub type TagMut<'a> = libcrux_traits::aead::typed_refs::TagMut<'a, $implementation>;
        #[doc = concat!("A reference to a ",stringify!($implementation), " nonce.")]
        pub type NonceRef<'a> = libcrux_traits::aead::typed_refs::NonceRef<'a, $implementation>;
    };
}

platform_mod!(AesGcm128);

pub mod portable {
    platform_mod!(PortableAesGcm128);
}
pub mod neon {
    platform_mod!(NeonAesGcm128);
}

pub mod x64 {
    platform_mod!(X64AesGcm128);
}
