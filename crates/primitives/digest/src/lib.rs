//! This crate provides digest implementations.
//!
//! - Blake2
//! - Sha2
//! - Sha3
//!
//! These can be used directly, using the `blake2`, `sha2` and `sha3` submodules.
//!
//!

#[cfg(any(feature = "sha2", feature = "sha3", feature = "blake2"))]
pub use libcrux_traits::digest::Hasher;

#[cfg(feature = "blake2")]
pub mod blake2 {
    //! ```rust
    //! use libcrux_digest::blake2::*;
    //! use libcrux_traits::digest::arrayref::Hash as _;
    //! let mut digest = [0; 32];
    //! Blake2bHash::hash(&mut digest, b"test data").unwrap();
    //! ```
    //!
    //! ```rust
    //! use libcrux_digest::blake2::*;
    //! let mut digest = [0; 32];
    //! let mut hasher = Blake2bHasher::new();
    //! hasher.update(b"test data").unwrap();
    //! hasher.finish(&mut digest);
    //! ```
    pub use libcrux_blake2::{Blake2bHash, Blake2bHasher, Blake2sHash, Blake2sHasher};
}

#[cfg(feature = "sha2")]
pub mod sha2 {
    //! ```rust
    //! use libcrux_digest::sha2::*;
    //! use libcrux_traits::digest::arrayref::Hash as _;
    //! let mut digest = [0; 28];
    //! Sha2_224::hash(&mut digest, b"test data").unwrap();
    //! ```
    //!
    //! ```rust
    //! use libcrux_digest::sha2::*;
    //! use libcrux_traits::digest::owned::Hash as _;
    //!
    //! let digest = Sha2_224::hash(b"test data").unwrap();
    //! ```
    //!
    //! ```rust
    //! use libcrux_digest::sha2::Sha2_224Hasher;
    //! let mut digest = [0; 28];
    //! let mut hasher = Sha2_224Hasher::default();
    //! hasher.update(b"test data").unwrap();
    //! hasher.finish(&mut digest);
    //! ```
    pub use libcrux_sha2::{
        Sha224Hash as Sha2_224, Sha224Hasher as Sha2_224Hasher, Sha256Hash as Sha2_256,
        Sha256Hasher as Sha2_256Hasher, Sha384Hash as Sha2_384, Sha384Hasher as Sha2_384Hasher,
        Sha512Hash as Sha2_512, Sha512Hasher as Sha2_512Hasher,
    };
}

#[cfg(feature = "sha3")]
pub mod sha3 {
    //! ```rust
    //! use libcrux_digest::sha3::*;
    //! use libcrux_traits::digest::arrayref::Hash as _;
    //! let mut digest = [0; 28];
    //! Sha3_224::hash(&mut digest, b"test data").unwrap();
    //! ```
    //!
    //! ```rust
    //! use libcrux_digest::sha3::*;
    //! use libcrux_traits::digest::owned::Hash as _;
    //!
    //! let digest = Sha3_224::hash(b"test data").unwrap();

    // TODO: also re-export the `Hasher` type aliases here?
    pub use libcrux_sha3::{Sha3_224, Sha3_256, Sha3_384, Sha3_512};
}
