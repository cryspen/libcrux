//! PSQ implementation backed by `classic-mceliece-rust`
//!
//! This module implements PSQ using ClassicMcEliece (parameter set
//! `mceliece460896f`) as the underlying KEM.

use classic_mceliece_rust::{
    decapsulate_boxed, encapsulate_boxed, keypair_boxed, Ciphertext, PublicKey, SecretKey,
    SharedSecret,
};

use libcrux_traits::kem::{KEMError, KeyPair, KEM};

use crate::traits::*;

/// A code-based KEM based on the McEliece cryptosystem.
pub struct ClassicMcEliece;

impl Encode for PublicKey<'_> {
    fn encode(&self) -> Vec<u8> {
        self.as_ref().to_vec()
    }
}

impl Encode for SharedSecret<'_> {
    fn encode(&self) -> Vec<u8> {
        self.as_ref().to_vec()
    }
}

impl Encode for Ciphertext {
    fn encode(&self) -> Vec<u8> {
        self.as_ref().to_vec()
    }
}

impl private::Seal for ClassicMcEliece {}

impl KEM for ClassicMcEliece {
    type Ciphertext = Ciphertext;
    type SharedSecret = SharedSecret<'static>;
    type EncapsulationKey = PublicKey<'static>;
    type DecapsulationKey = SecretKey<'static>;

    fn generate_key_pair(
        rng: &mut (impl rand::CryptoRng + rand::Rng),
    ) -> Result<KeyPair<SecretKey<'static>, PublicKey<'static>>, KEMError> {
        let (pk, sk) = keypair_boxed(rng);
        Ok((sk, pk))
    }

    fn encapsulate(
        ek: &Self::EncapsulationKey,
        rng: &mut (impl rand::CryptoRng + rand::Rng),
    ) -> Result<(Self::SharedSecret, Self::Ciphertext), KEMError> {
        let (enc, ss) = encapsulate_boxed(ek, rng);
        Ok((ss, enc))
    }

    fn decapsulate(
        dk: &Self::DecapsulationKey,
        ctxt: &Self::Ciphertext,
    ) -> Result<Self::SharedSecret, KEMError> {
        let ss = decapsulate_boxed(ctxt, dk);
        Ok(ss)
    }
}

impl PSQ for ClassicMcEliece {
    type InnerKEM = Self;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_classic_mceliece() {
        let mut rng = rand::thread_rng();
        let (sk, pk) = ClassicMcEliece::generate_key_pair(&mut rng).unwrap();
        let sctx = b"test context";
        let (psk_initiator, message) =
            ClassicMcEliece::encapsulate_psq(&pk, sctx, &mut rng).unwrap();

        let psk_responder = ClassicMcEliece::decapsulate_psq(&sk, &pk, &message, sctx).unwrap();
        assert_eq!(psk_initiator, psk_responder);
    }
}
