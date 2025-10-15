//! This module provides common interface traits for signature scheme implementations.

pub mod arrayref;
pub mod owned;
pub mod slice;

pub mod key_centric_owned;
pub mod key_centric_refs;

#[cfg(feature = "generic-tests")]
pub mod tests;
