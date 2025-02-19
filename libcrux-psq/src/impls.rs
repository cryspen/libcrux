//! PSQ implementation backed by `libcrux`.
//!
//! This module implements PSQ using the following underlying KEMs:
//! * `MLKem768`, a lattice-based post-quantum KEM, as specified in FIPS 203 (Draft)
//! * `XWingKemDraft02`, a hybrid post-quantum KEM combining X25519 and ML-KEM 768
//! * `X25519`, an elliptic-curve Diffie-Hellman based KEM. This
//!   implementation is available with feature `test-utils` and using this
//!   KEM *does not provide post-quantum security*. We include it for
//!   testing and benchmarking.

use crate::traits::*;
use libcrux_kem::{Ct, PrivateKey, PublicKey, Ss};
use libcrux_traits::kem::{KEMError, KeyPair, KEM};

macro_rules! libcrux_impl {
    ($alg:ident, $docstring:literal) => {
        #[doc = $docstring]
        pub struct $alg;

        impl $alg {
            fn algorithm() -> libcrux_kem::Algorithm {
                libcrux_kem::Algorithm::$alg
            }
        }

        impl crate::traits::private::Seal for $alg {}

        impl KEM for $alg {
            type Ciphertext = Ct;
            type EncapsulationKey = PublicKey;
            type DecapsulationKey = PrivateKey;
            type SharedSecret = Ss;

            fn encapsulate(
                ek: &Self::EncapsulationKey,
                rng: &mut (impl rand::CryptoRng + rand::Rng),
            ) -> Result<(Self::SharedSecret, Self::Ciphertext), KEMError> {
                ek.encapsulate(rng).map_err(|_| KEMError::Encapsulation)
            }

            fn decapsulate(
                dk: &Self::DecapsulationKey,
                ctxt: &Self::Ciphertext,
            ) -> Result<Self::SharedSecret, libcrux_traits::kem::KEMError> {
                ctxt.decapsulate(dk).map_err(|_| KEMError::Decapsulation)
            }

            fn generate_key_pair(
                rng: &mut (impl rand::CryptoRng + rand::Rng),
            ) -> Result<KeyPair<PrivateKey, PublicKey>, libcrux_traits::kem::KEMError> {
                libcrux_kem::key_gen(Self::algorithm(), rng).map_err(|_| KEMError::KeyGeneration)
            }
        }

        impl crate::traits::PSQ for $alg {
            type InnerKEM = Self;
        }
    };
}

#[cfg(feature = "test-utils")]
libcrux_impl!(
    X25519,
    "An elliptic-curve Diffie-Hellman based KEM (Does not provide post-quantum security)"
);
libcrux_impl!(
    MlKem768,
    "ML-KEM 768, a lattice-based post-quantum KEM, as specified in FIPS 203 (Draft)"
);
libcrux_impl!(
    XWingKemDraft02,
    "A hybrid post-quantum KEM combining X25519 and ML-KEM 768"
);

impl Encode for PublicKey {
    fn encode(&self) -> Vec<u8> {
        self.encode()
    }
}

impl Encode for Ct {
    fn encode(&self) -> Vec<u8> {
        self.encode()
    }
}

impl Encode for Ss {
    fn encode(&self) -> Vec<u8> {
        self.encode()
    }
}

#[cfg(test)]
mod tests {
    #![allow(non_snake_case)]
    use super::*;

    macro_rules! libcrux_test {
        ($alg:ident) => {
            #[test]
            fn $alg() {
                let mut rng = rand::thread_rng();
                let (sk, pk) = $alg::generate_key_pair(&mut rng).unwrap();
                let sctx = b"test context";
                let (psk_initiator, message) = $alg::encapsulate_psq(&pk, sctx, &mut rng).unwrap();

                let psk_responder = $alg::decapsulate_psq(&sk, &pk, &message, sctx).unwrap();
                assert_eq!(psk_initiator, psk_responder);
            }
        };
    }

    #[cfg(feature = "test-utils")]
    libcrux_test!(X25519);
    libcrux_test!(MlKem768);
    libcrux_test!(XWingKemDraft02);
}
