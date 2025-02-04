//! PSQ implementation backed by `libcrux`.
//!
//! This module implements PSQ using the following underlying KEMs:
//! * `MLKem768`, a lattice-based post-quantum KEM, as specified in FIPS 203 (Draft)
//! * `XWingKemDraft02`, a hybrid post-quantum KEM combining X25519 and ML-KEM 768
//! * `X25519`, an elliptic-curve Diffie-Hellman based KEM. This
//!   implementation is available with feature `non-pq` and using this
//!   KEM *does not provide post-quantum security*. We include it for
//!   testing and benchmarking.

use crate::psq_traits::*;

macro_rules! libcrux_impl {
    ($alg:ident, $docstring:literal) => {
        #[doc = $docstring]
        pub struct $alg;
        impl private::Seal for $alg {}

        impl LibcruxKEM for $alg {
            fn algorithm() -> libcrux_kem::Algorithm {
                libcrux_kem::Algorithm::$alg
            }
        }
    };
}

#[cfg(feature = "non-pq")]
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

/// Wrapper around `libcrux_kem` encapsulation keys
pub struct LibcruxPSQEncapsKey(libcrux_kem::PublicKey);

impl Encode for LibcruxPSQEncapsKey {
    fn encode(&self) -> Vec<u8> {
        self.0.encode()
    }
}

/// Wrapper around `libcrux_kem` decapsulation keys.
pub struct LibcruxPSQDecapsKey(libcrux_kem::PrivateKey);

/// Wrapper around `libcrux_kem` ciphertexts.
pub struct LibcruxPSQCiphertext(libcrux_kem::Ct);

impl Encode for LibcruxPSQCiphertext {
    fn encode(&self) -> Vec<u8> {
        self.0.encode()
    }
}

/// Wrapper around `libcrux_kem` shared secrets.
pub struct LibcruxPSQSharedSecret(libcrux_kem::Ss);

impl Encode for LibcruxPSQSharedSecret {
    fn encode(&self) -> Vec<u8> {
        self.0.encode()
    }
}

trait LibcruxKEM: private::Seal {
    fn algorithm() -> libcrux_kem::Algorithm;
}

impl<T> crate::psq_traits::KEM<'_> for T
where
    T: LibcruxKEM,
{
    type Ciphertext = LibcruxPSQCiphertext;
    type EncapsulationKey = LibcruxPSQEncapsKey;
    type DecapsulationKey = LibcruxPSQDecapsKey;
    type SharedSecret = LibcruxPSQSharedSecret;

    fn encapsulate(
        ek: &Self::EncapsulationKey,
        rng: &mut (impl rand::CryptoRng + rand::Rng),
    ) -> Result<(Self::SharedSecret, Self::Ciphertext), crate::Error> {
        let (ss, enc) = ek.0.encapsulate(rng)?;
        Ok((LibcruxPSQSharedSecret(ss), LibcruxPSQCiphertext(enc)))
    }

    fn decapsulate(
        dk: &Self::DecapsulationKey,
        ctxt: &Self::Ciphertext,
    ) -> Result<Self::SharedSecret, crate::Error> {
        let ss = ctxt.0.decapsulate(&dk.0)?;
        Ok(LibcruxPSQSharedSecret(ss))
    }
}

impl<T: LibcruxKEM> crate::psq_traits::PSQ<'_> for T {
    type InnerKEM = Self;

    fn generate_key_pair(
        rng: &mut (impl rand::CryptoRng + rand::Rng),
    ) -> Result<
        (
            <Self::InnerKEM as KEM<'_>>::DecapsulationKey,
            <Self::InnerKEM as KEM<'_>>::EncapsulationKey,
        ),
        crate::Error,
    > {
        let (sk, pk) = libcrux_kem::key_gen(Self::algorithm(), rng)?;
        Ok((LibcruxPSQDecapsKey(sk), LibcruxPSQEncapsKey(pk)))
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

    #[cfg(feature = "non-pq")]
    libcrux_test!(X25519);
    libcrux_test!(MlKem768);
    libcrux_test!(XWingKemDraft02);
}
