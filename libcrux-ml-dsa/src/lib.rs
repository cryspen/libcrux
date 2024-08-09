pub fn print_stack(f: &str) {
    eprintln!(
        "{f} remaining stack: {} KiB | stack pointer: {:p}",
        stacker::remaining_stack().unwrap() / 1024,
        &psm::stack_pointer()
    );
}

mod arithmetic;
mod constants;
mod encoding;
mod hash_functions;
mod instantiations;
mod matrix;
mod ml_dsa_generic;
mod ntt;
mod polynomial;
mod sample;
mod simd;
mod types;
mod utils;

// Public interface

pub use {ml_dsa_generic::VerificationError, types::*};

pub mod ml_dsa_44;
pub mod ml_dsa_65;
pub mod ml_dsa_87;
