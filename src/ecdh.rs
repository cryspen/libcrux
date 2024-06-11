//! # ECDH
//!
//! Depending on the platform and available features the most efficient implementation
//! is chosen.
//!
//! ## x25519
//! For x25519 the portable HACL implementation is used unless running on an x64
//! CPU with BMI2 and ADX support. In this case the libjade implementation is
//! used.
//!
//! ## P256
//! For P256 the portable HACL implementation is used.

pub use libcrux_ecdh::Error;
pub use libcrux_ecdh::LowLevelError;

pub use libcrux_ecdh::Algorithm;

pub use libcrux_ecdh::x25519_generate_secret;
pub use libcrux_ecdh::x25519_key_gen;

pub use libcrux_ecdh::p256_generate_secret;
pub use libcrux_ecdh::p256_key_gen;
pub use libcrux_ecdh::p256_validate_scalar;

pub use libcrux_ecdh::derive;
pub use libcrux_ecdh::p256_derive;

pub use libcrux_ecdh::secret_to_public;

pub use libcrux_ecdh::validate_scalar;

pub use libcrux_ecdh::generate_secret;
pub use libcrux_ecdh::key_gen;
