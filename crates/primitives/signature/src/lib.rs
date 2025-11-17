//! This crate provides signature functionality.
//!
//! We currently support three signature algorithms:
//!
//! - ecdsa-p256
//! - ed25519
//! - ML-DSA

#[cfg(any(feature = "ecdsa", feature = "ed25519", feature = "mldsa"))]
pub use libcrux_traits::signature::{SignConsts, SignTypes};

#[cfg(feature = "ecdsa")]
pub mod ecdsa {
    pub mod p256 {
        //! ```rust
        //! use libcrux_signature::ecdsa::p256::{
        //!   Nonce, sha2_256::{EcdsaP256, KeyPair, SigningKey, VerificationKey}
        //! };
        //!
        //! // generate a new nonce
        //! use rand::TryRngCore;
        //! let mut rng = rand::rngs::OsRng;
        //! let nonce = Nonce::random(&mut rng.unwrap_mut()).unwrap();
        //!
        //! // generate a new signature keypair from random bytes
        //! let KeyPair { signing_key, verification_key } =
        //! EcdsaP256::generate_key_pair(&mut rng.unwrap_mut()).unwrap();
        //!
        //! // sign
        //! let signature = signing_key.sign(b"payload", &nonce).unwrap();
        //!
        //! // verify
        //! verification_key.verify(b"payload", &signature).unwrap();
        //! ```
        pub use libcrux_ecdsa::key_centric_apis::{sha2_256, sha2_384, sha2_512};
        pub use libcrux_ecdsa::p256::Nonce;
    }
}

#[cfg(feature = "ed25519")]
pub mod ed25519 {
    //! ```rust
    //! use libcrux_signature::ed25519::{Ed25519, KeyPair};
    //!
    //! use rand::TryRngCore;
    //! let mut rng = rand::rngs::OsRng;
    //! // generate a new signature keypair from random bytes
    //! // requires `rand` feature
    //! let KeyPair { signing_key, verification_key }
    //!     = Ed25519::generate_key_pair(&mut rng.unwrap_mut());
    //!
    //! // sign
    //! let signature = signing_key.sign(b"payload").unwrap();
    //!
    //! // verify
    //! verification_key.verify(b"payload", &signature).unwrap();
    //! ```
    pub use libcrux_ed25519::key_centric_apis::{
        Ed25519, KeyPair, SigningKey, SigningKeyRef, VerificationKey, VerificationKeyRef,
    };
}

#[cfg(feature = "mldsa")]
pub mod mldsa {
    //! ```rust
    //! use libcrux_signature::mldsa::{MlDsa44, SigningKey, KeyPair, VerificationKey};
    //!

    //! use rand::TryRngCore;
    //! let mut rng = rand::rngs::OsRng;
    //!
    //! // generate a new signature keypair from random bytes
    //! // requires `rand` feature
    //! let KeyPair { signing_key, verification_key }
    //!     = MlDsa44::generate_key_pair(&mut rng.unwrap_mut());
    //!
    //! // sign
    //! let signature = signing_key.sign(b"payload", b"context", [2; 32]).unwrap();
    //!
    //! // verify
    //! verification_key.verify(b"payload", &signature, b"context").unwrap();
    //! ```
    //!
    //! ```rust
    //! use libcrux_signature::mldsa::{MlDsa44, SigningKeyRef};
    //! use libcrux_traits::signature::SignConsts;
    //!
    //!
    //! // signing key from bytes
    //! let signing_key = SigningKeyRef::from_slice(&[1; 2560]).unwrap();
    //!
    //! // sign with randomness
    //! let mut signature = [0u8; MlDsa44::SIGNATURE_LEN];
    //! signing_key.sign(b"payload", &mut signature, b"context", [2; 32]).unwrap();
    //!
    //! ```
    pub use libcrux_ml_dsa::key_centric_apis::ml_dsa_44::{
        KeyPair, MlDsa44, Signature, SigningKey, SigningKeyRef, VerificationKey, VerificationKeyRef,
    };
}
