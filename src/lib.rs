//! # libcrux
//! 
//! The unified, formally verified, cryptography library.

mod hw_detection;

// TODO: Make languages private

// Coq
pub mod cobra;

// HACL
pub mod hacl;

// Jasmin
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub mod jasmin;

// libcrux
pub mod aead;
pub mod ecdh;
pub mod digest;
