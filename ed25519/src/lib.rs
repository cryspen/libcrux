#![no_std]

mod hacl {
    //! This module contains generated hacl code.

    pub(crate) mod ed25519;
    pub(crate) mod ed25519_precomptable;
}

mod impl_hacl;
mod impl_signature_trait;

pub use impl_hacl::*;
