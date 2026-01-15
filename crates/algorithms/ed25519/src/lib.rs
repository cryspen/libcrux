#![no_std]

mod hacl {
    //! This module contains generated hacl code.

    pub(crate) mod ed25519;
    pub(crate) mod ed25519_precomptable;
}

mod impl_hacl;
pub(crate) mod key_centric_apis;

pub use impl_hacl::*;
