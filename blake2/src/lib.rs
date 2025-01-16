//#![no_std]

mod hacl {
    //! This module contains generated hacl code.

    pub(crate) mod hash_blake2b;
    pub(crate) mod hash_blake2s;
    pub(crate) mod impl_blake2_constants;
}

mod impl_hacl;

pub use impl_hacl::*;
