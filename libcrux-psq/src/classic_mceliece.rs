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

// This is only here because `classic-mceliece-rust` still depends on
// `rand` version `0.8.0`.
struct McElieceRng<'a, T: rand::CryptoRng> {
    inner_rng: &'a mut T,
}

impl<'a, T: rand::CryptoRng> McElieceRng<'a, T> {
    fn new(inner_rng: &'a mut T) -> Self {
        Self { inner_rng }
    }
}

impl<'a, T: rand::CryptoRng> rand_old::RngCore for McElieceRng<'a, T> {
    fn next_u32(&mut self) -> u32 {
        self.inner_rng.next_u32()
    }
    fn next_u64(&mut self) -> u64 {
        self.inner_rng.next_u64()
    }
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.inner_rng.fill_bytes(dest)
    }
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_old::Error> {
        Ok(self.inner_rng.fill_bytes(dest))
    }
}

impl<'a, T: rand::CryptoRng> rand_old::CryptoRng for McElieceRng<'a, T> {}

impl KEM for ClassicMcEliece {
    /// The KEM's ciphertext.
    type Ciphertext = Ciphertext;
    /// The KEM's shared secret.
    type SharedSecret = SharedSecret<'static>;
    /// The KEM's encapsulation key.
    type EncapsulationKey = PublicKey<'static>;
    /// The KEM's decapsulation key.
    type DecapsulationKey = SecretKey<'static>;

    /// Generate a pair of encapsulation and decapsulation keys.
    fn generate_key_pair(
        rng: &mut (impl rand::CryptoRng + rand::Rng),
    ) -> Result<KeyPair<SecretKey<'static>, PublicKey<'static>>, KEMError> {
        let mut rng = McElieceRng::new(rng);
        let (pk, sk) = keypair_boxed(&mut rng);
        Ok((sk, pk))
    }

    /// Encapsulate a shared secret towards a given encapsulation key.
    fn encapsulate(
        ek: &Self::EncapsulationKey,
        rng: &mut (impl rand::CryptoRng + rand::Rng),
    ) -> Result<(Self::SharedSecret, Self::Ciphertext), KEMError> {
        let mut rng = McElieceRng::new(rng);
        let (enc, ss) = encapsulate_boxed(ek, &mut rng);
        Ok((ss, enc))
    }

    /// Decapsulate a shared secret.
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
