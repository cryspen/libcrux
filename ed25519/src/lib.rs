#![no_std]

pub mod hacl {
    //! This module contains generated hacl code.

    pub mod ed25519;
    pub mod ed25519_precomptable;
}

mod impl_hacl;

pub use impl_hacl::*;
