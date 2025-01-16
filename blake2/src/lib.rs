//#![no_std]

pub mod hacl {
    //! This module contains generated hacl code.

    pub mod hash_blake2b;
    pub mod hash_blake2s;
    pub mod impl_blake2_constants;
}

mod impl_hacl;

pub use impl_hacl::*;
