#![no_std]
// The NTT layer-0/1/2 functional-correctness proof annotations attach a dense
// stack of `#[hax_lib::fstar::before(...)]` blocks to ntt_at_layer_0, which
// overflows the default proc-macro recursion limit during `#[_hax::json]`
// expansion.  Compile-time only — does not affect extracted F* or runtime.
#![recursion_limit = "1024"]
#![deny(unsafe_code)]
#![deny(unused_qualifications)]

#[cfg(feature = "std")]
extern crate std;

// Crate-wide `proof!` annotation marker (see proof_macros.rs). `#[macro_use]`
// must precede the modules that use it so the macro is in scope for them.
#[macro_use]
mod proof_macros;

mod arithmetic;
mod constants;
mod encoding;
mod hash_functions;
mod helper;
mod matrix;
mod ml_dsa_generic;
mod ntt;
mod polynomial;
mod pre_hash;
#[cfg(hax)]
mod proof_utils;
mod sample;
mod samplex4;
mod simd;

#[cfg(hax)]
mod specs;

mod types;

// Public interface

pub use types::*;

pub use crate::constants::KEY_GENERATION_RANDOMNESS_SIZE;
pub use crate::constants::SIGNING_RANDOMNESS_SIZE;

#[cfg(feature = "mldsa44")]
pub mod ml_dsa_44;

#[cfg(feature = "mldsa65")]
pub mod ml_dsa_65;

#[cfg(feature = "mldsa87")]
pub mod ml_dsa_87;
