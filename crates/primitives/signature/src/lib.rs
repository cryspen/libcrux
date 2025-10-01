#[cfg(any(feature = "ecdsa", feature = "ed25519", feature = "mldsa"))]
pub use libcrux_traits::signature::{
    key_centric_owned::{KeyPair, SigningKey, VerificationKey},
    key_centric_refs::{SigningKeyRef, VerificationKeyRef},
    owned::Sign,
};

#[cfg(feature = "ecdsa")]
pub mod ecdsa {
    pub mod p256 {
        //! ```rust
        //! use libcrux_signature::ecdsa::p256::{P256Signer as P256, Sha2_512, Nonce};
        //! use libcrux_signature::{Sign, KeyPair, SigningKey, VerificationKey};
        //!
        //! // generate a new nonce
        //! use rand::TryRngCore;
        //! let mut rng = rand::rngs::OsRng;
        //! let nonce = Nonce::random(&mut rng.unwrap_mut()).unwrap();
        //!
        //! // generate a new signature keypair from random bytes
        //! let KeyPair { signing_key, verification_key } =
        //! P256::<Sha2_512>::generate_key_pair(&mut rng.unwrap_mut()).unwrap();
        //!
        //! // sign
        //! let signature = signing_key.sign(b"payload", &nonce).unwrap();
        //!
        //! // verify
        //! verification_key.verify(b"payload", &signature, ()).unwrap();
        //! ```
        pub use libcrux_ecdsa::signers::p256::{
            Nonce, Sha2_256, Sha2_384, Sha2_512, Signer as P256Signer,
        };
    }
}

#[cfg(feature = "ed25519")]
pub mod ed25519 {
    //! ```rust
    //! use libcrux_signature::ed25519::Ed25519;
    //! use libcrux_signature::{Sign, KeyPair, SigningKey, VerificationKey};
    //!
    //! use rand::TryRngCore;
    //! let mut rng = rand::rngs::OsRng;
    //! // generate a new signature keypair from random bytes
    //! let KeyPair { signing_key, verification_key }
    //!     = Ed25519::generate_key_pair(&mut rng.unwrap_mut()).unwrap();
    //!
    //! // sign
    //! let signature = signing_key.sign(b"payload", ()).unwrap();
    //!
    //! // verify
    //! verification_key.verify(b"payload", &signature, ()).unwrap();
    //! ```
    pub use libcrux_ed25519::signers::Signer as Ed25519;
}

#[cfg(feature = "mldsa")]
pub mod mldsa {
    //! ```rust
    //! use libcrux_signature::mldsa::{Context, MlDsa44, impl_context};
    //! use libcrux_signature::{Sign, KeyPair, SigningKey, VerificationKey};
    //!
    //! // set application context
    //! impl_context!(AppContext, b"context");

    //! use rand::TryRngCore;
    //! let mut rng = rand::rngs::OsRng;
    //!
    //! // generate a new signature keypair from random bytes
    //! let KeyPair { signing_key, verification_key }
    //!     = MlDsa44::<AppContext>::generate_key_pair(&mut rng.unwrap_mut()).unwrap();
    //!
    //! // sign
    //! let signature = signing_key.sign(b"payload", [2; 32]).unwrap();
    //!
    //! // verify
    //! verification_key.verify(b"payload", &signature, ()).unwrap();
    //! ```
    //!
    //! ```rust
    //! use libcrux_signature::mldsa::{Context, MlDsa44, impl_context};
    //! use libcrux_signature::SigningKeyRef;
    //!
    //! // set application context
    //! impl_context!(AppContext, b"context");
    //!
    //! // signing key from bytes
    //! let signing_key = SigningKeyRef::<MlDsa44<AppContext>>::from_bytes([1; MlDsa44::<AppContext>::SIGNING_KEY_LEN].as_ref()).unwrap();
    //!
    //! // sign with randomness
    //! signing_key.sign(b"payload", [2; 32]).unwrap();
    //!
    //! ```
    pub use libcrux_ml_dsa::signers::{
        impl_context, Context, MlDsa44Signer as MlDsa44, MlDsa65Signer as MlDsa65,
        MlDsa87Signer as MlDsa87,
    };
}
