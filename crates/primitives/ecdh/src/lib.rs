#[cfg(any(feature = "p256", feature = "curve25519"))]
pub use libcrux_traits::ecdh::key_centric_owned::{Pair, Public, Secret};

#[cfg(feature = "p256")]
pub mod p256 {
    pub use libcrux_p256::ecdh_api::*;
    pub use libcrux_p256::P256;
}

#[cfg(feature = "curve25519")]
pub mod curve25519 {
    //! ```rust
    //! use libcrux_ecdh_new::curve25519::X25519;
    //! use libcrux_ecdh_new::Pair;
    //!
    //! use rand::RngCore;
    //! let mut rng = rand::rng();
    //!
    //! let mut randomness = [0u8; 32];
    //!
    //! rng.fill_bytes(&mut randomness);
    //! let x25519_key_pair_a = Pair::<X25519>::generate(&randomness).unwrap();
    //!
    //! rng.fill_bytes(&mut randomness);
    //! let let x25519_key_pair_b = Pair::<X25519>::generate(&randomness).unwrap();
    //!
    //! let derived_a = x25519_key_pair_a.secret().derive_ecdh(x25519_key_pair_b.public()).unwrap();
    //! let derived_b = x25519_key_pair_b.public().derive_ecdh(x25519_key_pair_a.secret()).unwrap();
    //!
    //! assert_eq!(derived_a, derived_b);
    //! ```
    pub use libcrux_curve25519::ecdh_api::*;
    pub use libcrux_curve25519::X25519;
}
