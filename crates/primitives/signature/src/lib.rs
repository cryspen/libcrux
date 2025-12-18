//! This crate provides signature functionality.
//!
//! We currently support three signature algorithms:
//!
//! - ECDSA-P256
//! - Ed25519
//! - ML-DSA

#[doc(inline)]
#[cfg(any(feature = "ecdsa", feature = "ed25519", feature = "mldsa"))]
pub use libcrux_traits::signature::{SignConsts, WrongLengthError};

#[cfg(feature = "ecdsa")]
pub mod ecdsa {
    //! APIs for ECDSA
    pub mod p256 {
        //! APIs for ECDSA-P256
        //!
        //! ### Key-centric APIs
        //!
        //! #### Key-centric (owned)
        //! ```rust
        //! use libcrux_signature::ecdsa::p256::{
        //!   Nonce, sha2_256::{KeyPair, SigningKey, VerificationKey}
        //! };
        //!
        //! // generate a new nonce
        //! use rand::TryRngCore;
        //! let mut rng = rand::rngs::OsRng;
        //! let nonce = Nonce::random(&mut rng.unwrap_mut()).unwrap();
        //!
        //! // generate a new signature keypair from random bytes
        //! let KeyPair { signing_key, verification_key } =
        //!     KeyPair::generate(&mut rng.unwrap_mut()).unwrap();
        //!
        //! // sign
        //! let signature = signing_key.sign(b"payload", &nonce).unwrap();
        //!
        //! // verify
        //! verification_key.verify(b"payload", &signature).unwrap();
        //! ```
        //!
        //! #### Key-centric (reference)
        //! ```rust
        //! # use libcrux_signature::ecdsa::p256::{
        //! #   Nonce, sha2_256::{SigningKeyRef, VerificationKeyRef, EcdsaP256}
        //! # };
        //! # use libcrux_signature::SignConsts;
        //! #
        //! # use rand::{RngCore, TryRngCore};
        //! # let mut rng = rand::rngs::OsRng;
        //! # let mut rng = rng.unwrap_mut();
        //! # // generate a new nonce
        //! # let nonce = Nonce::random(&mut rng).unwrap();
        //! #
        //! # let mut signing_key = [0u8; EcdsaP256::SIGNING_KEY_LEN];
        //! # let mut verification_key = [0u8; EcdsaP256::VERIFICATION_KEY_LEN];
        //! # let mut bytes = [1u8; EcdsaP256::RAND_KEYGEN_LEN];
        //! # rng.fill_bytes(&mut bytes);
        //! # EcdsaP256::keygen(&mut signing_key, &mut verification_key, bytes).unwrap();
        //!
        //! // create the key structs from byte slices
        //! let signing_key = SigningKeyRef::from_slice(&signing_key).unwrap();
        //! let verification_key = VerificationKeyRef::from_slice(&verification_key).unwrap();
        //!
        //! // signature buffer
        //! let mut signature = [0u8; EcdsaP256::SIGNATURE_LEN];
        //!
        //! // sign
        //! signing_key.sign(b"payload", &mut signature, &nonce).unwrap();
        //!
        //! // verify
        //! verification_key.verify(b"payload", &signature).unwrap();
        //! ```
        //! ### Slice-based
        //! ```rust
        //! # use libcrux_signature::ecdsa::p256::{sha2_256::EcdsaP256, Nonce};
        //! # use libcrux_signature::SignConsts;
        //! #
        //! # use rand::{RngCore, TryRngCore};
        //! # let mut rng = rand::rngs::OsRng;
        //! # let mut rng = rng.unwrap_mut();

        //! # // generate a new nonce
        //! # let nonce = Nonce::random(&mut rng).unwrap();
        //! #
        //! # let mut signing_key = [0u8; EcdsaP256::SIGNING_KEY_LEN];
        //! # let mut verification_key = [0u8; EcdsaP256::VERIFICATION_KEY_LEN];
        //! # let mut bytes = [1u8; EcdsaP256::RAND_KEYGEN_LEN];
        //! # rng.fill_bytes(&mut bytes);
        //! # EcdsaP256::keygen(&mut signing_key, &mut verification_key, bytes).unwrap();
        //! #
        //! // signature buffer
        //! let mut signature = [0u8; EcdsaP256::SIGNATURE_LEN];
        //!
        //! // sign
        //! EcdsaP256::sign(&signing_key, b"payload", &mut signature, &nonce).unwrap();
        //!
        //! // verify
        //! EcdsaP256::verify(&verification_key, b"payload", &signature).unwrap();
        //! ```
        #[doc(inline)]
        pub use libcrux_ecdsa::{
            key_centric_apis::{sha2_256, sha2_384, sha2_512},
            p256::Nonce,
        };
    }
}

#[cfg(feature = "ed25519")]
pub mod ed25519 {
    //! APIs for Ed25519
    //!
    //! ### Key-centric APIs
    //!
    //! #### Key-centric (owned)
    //! ```rust
    //! use libcrux_signature::ed25519::KeyPair;
    //!
    //! use rand::TryRngCore;
    //! let mut rng = rand::rngs::OsRng;
    //!
    //! // generate a new signature keypair from random bytes
    //! // requires `rand` feature
    //! let KeyPair { signing_key, verification_key }
    //!     = KeyPair::generate(&mut rng.unwrap_mut());
    //!
    //! // sign
    //! let signature = signing_key.sign(b"payload").unwrap();
    //!
    //! // verify
    //! verification_key.verify(b"payload", &signature).unwrap();
    //! ```
    //! #### Key-centric (reference)
    //! ```rust
    //! # use libcrux_signature::ed25519::{
    //! #   SigningKeyRef, VerificationKeyRef, Ed25519,
    //! # };
    //! # use libcrux_signature::SignConsts;
    //! #
    //! # use rand::{RngCore, TryRngCore};
    //! # let mut rng = rand::rngs::OsRng;
    //! # let mut rng = rng.unwrap_mut();
    //! #
    //! # let mut signing_key = [0u8; Ed25519::SIGNING_KEY_LEN];
    //! # let mut verification_key = [0u8; Ed25519::VERIFICATION_KEY_LEN];
    //! # let mut bytes = [1u8; Ed25519::RAND_KEYGEN_LEN];
    //! # rng.fill_bytes(&mut bytes);
    //! # Ed25519::keygen(&mut signing_key, &mut verification_key, bytes).unwrap();
    //! // create the key structs from byte slices
    //! let signing_key = SigningKeyRef::from_slice(&signing_key).unwrap();
    //! let verification_key = VerificationKeyRef::from_slice(&verification_key).unwrap();
    //!
    //! // signature buffer
    //! let mut signature = [0u8; Ed25519::SIGNATURE_LEN];
    //!
    //! // sign
    //! signing_key.sign(b"payload", &mut signature).unwrap();
    //!
    //! // verify
    //! verification_key.verify(b"payload", &signature).unwrap();
    //! ```
    //! ### Slice-based
    //! ```rust
    //! # use libcrux_signature::ed25519::Ed25519;
    //! # use libcrux_signature::SignConsts;
    //! #
    //! # use rand::{RngCore, TryRngCore};
    //! # let mut rng = rand::rngs::OsRng;
    //! # let mut rng = rng.unwrap_mut();
    //! #
    //! # let mut signing_key = [0u8; Ed25519::SIGNING_KEY_LEN];
    //! # let mut verification_key = [0u8; Ed25519::VERIFICATION_KEY_LEN];
    //! # let mut bytes = [1u8; Ed25519::RAND_KEYGEN_LEN];
    //! # rng.fill_bytes(&mut bytes);
    //! # Ed25519::keygen(&mut signing_key, &mut verification_key, bytes).unwrap();
    //! #
    //! // signature buffer
    //! let mut signature = [0u8; Ed25519::SIGNATURE_LEN];
    //!
    //! // sign
    //! Ed25519::sign(&signing_key, b"payload", &mut signature).unwrap();
    //!
    //! // verify
    //! Ed25519::verify(&verification_key, b"payload", &signature).unwrap();
    //! ```
    #[doc(inline)]
    pub use libcrux_ed25519::key_centric_apis::{
        slice, Ed25519, KeyPair, SigningError, SigningKey, SigningKeyRef, VerificationError,
        VerificationKey, VerificationKeyRef,
    };
}

#[cfg(feature = "mldsa")]
pub mod mldsa {
    //! APIs for ML-DSA
    //!
    //! ### Key-centric APIs
    //!
    //! #### Key-centric (owned)
    //! ```rust
    //! use libcrux_signature::mldsa::ml_dsa_44::{SigningKey, KeyPair, VerificationKey};
    //!
    //! use rand::{RngCore, TryRngCore};
    //! let mut rng = rand::rngs::OsRng;
    //! let mut rng = rng.unwrap_mut();
    //!
    //! // generate a new signature keypair from random bytes
    //! // requires `rand` feature
    //! let KeyPair { signing_key, verification_key }
    //!     = KeyPair::generate(&mut rng);
    //!
    //! // sign
    //! let mut signing_randomness = [0; 32];
    //! rng.fill_bytes(&mut signing_randomness);
    //! let signature = signing_key.sign(b"payload", b"context", signing_randomness).unwrap();
    //!
    //! // verify
    //! verification_key.verify(b"payload", &signature, b"context").unwrap();
    //! ```
    //! #### Key-centric (reference)
    //! ```rust
    //! # use libcrux_signature::mldsa::ml_dsa_44::{
    //! #   SigningKeyRef, VerificationKeyRef, MlDsa44,
    //! # };
    //! # use libcrux_signature::SignConsts;
    //! #
    //! # use rand::{RngCore, TryRngCore};
    //! # let mut rng = rand::rngs::OsRng;
    //! # let mut rng = rng.unwrap_mut();
    //! #
    //! # let mut signing_key = [0u8; MlDsa44::SIGNING_KEY_LEN];
    //! # let mut verification_key = [0u8; MlDsa44::VERIFICATION_KEY_LEN];
    //! # let mut bytes = [1u8; MlDsa44::RAND_KEYGEN_LEN];
    //! # rng.fill_bytes(&mut bytes);
    //! # MlDsa44::keygen(&mut signing_key, &mut verification_key, bytes).unwrap();
    //! #
    //! // create the key structs from byte slices
    //! let signing_key = SigningKeyRef::from_slice(&signing_key).unwrap();
    //! let verification_key = VerificationKeyRef::from_slice(&verification_key).unwrap();
    //!
    //! // signature buffer
    //! let mut signature = [0u8; MlDsa44::SIGNATURE_LEN];
    //!
    //! // sign
    //! let mut signing_randomness = [0; 32];
    //! rng.fill_bytes(&mut signing_randomness);
    //! signing_key.sign(b"payload", &mut signature, b"context", signing_randomness).unwrap();
    //!
    //! // verify
    //! verification_key.verify(b"payload", &signature, b"context").unwrap();
    //! ```
    //! ### Slice-based
    //! ```rust
    //! # use libcrux_signature::mldsa::ml_dsa_44::MlDsa44;
    //! # use libcrux_signature::SignConsts;
    //! #
    //! # use rand::{RngCore, TryRngCore};
    //! # let mut rng = rand::rngs::OsRng;
    //! # let mut rng = rng.unwrap_mut();
    //! #
    //! # let mut signing_key = [0u8; MlDsa44::SIGNING_KEY_LEN];
    //! # let mut verification_key = [0u8; MlDsa44::VERIFICATION_KEY_LEN];
    //! # let mut bytes = [1u8; MlDsa44::RAND_KEYGEN_LEN];
    //! # rng.fill_bytes(&mut bytes);
    //! # MlDsa44::keygen(&mut signing_key, &mut verification_key, bytes).unwrap();
    //! #
    //! // signature buffer
    //! let mut signature = [0u8; MlDsa44::SIGNATURE_LEN];
    //!
    //! // sign
    //! let mut signing_randomness = [0; 32];
    //! rng.fill_bytes(&mut signing_randomness);
    //! MlDsa44::sign(&signing_key, b"payload", &mut signature, b"context", signing_randomness).unwrap();
    //!
    //! // verify
    //! MlDsa44::verify(&verification_key, b"payload", &signature, b"context").unwrap();
    //! ```
    #[doc(inline)]
    pub use libcrux_ml_dsa::key_centric_apis::{ml_dsa_44, ml_dsa_65, ml_dsa_87};
}
