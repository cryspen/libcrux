//! Wycheproof Known Answer Tests

#[cfg(feature = "ecdh")]
pub mod ecdh;

#[cfg(feature = "mldsa")]
pub mod mldsa;

#[cfg(feature = "mlkem")]
pub mod mlkem;

pub mod schema_common;
pub use schema_common::TestResult;
