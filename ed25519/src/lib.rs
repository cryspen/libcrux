#![no_std]

#[cfg(feature = "hacl")]
pub mod hacl {
    //! This module contains generated hacl code.

    pub mod ed25519;
    pub mod ed25519_precomptable;
}

#[cfg(feature = "hacl")]
mod impl_hacl;

#[cfg(feature = "portable_hacl")]
pub use impl_hacl::*;
