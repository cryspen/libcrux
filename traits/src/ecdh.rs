//! This module provides a common interface trait for Elliptic Curve
//! Diffie-Hellman (ECDH) key exchange.

pub mod arrayref;
// pub mod key_centric_refs;
pub mod key_centric_owned;
pub mod owned;
pub mod slice;
