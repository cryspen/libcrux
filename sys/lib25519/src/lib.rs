//! FFI bindings to lib25519 cryptographic library.
//!
//! This crate provides Rust bindings to the lib25519 library, which implements
//! Curve25519 elliptic curve cryptography operations.

#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(missing_docs)]

include!("./bindings.rs");
