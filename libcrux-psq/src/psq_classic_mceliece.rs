//! PSQ implementation backed by `classic-mceliece-rust`
//!
//! This module implements PSQ using ClassicMcEliece (parameter set
//! `mceliece460896f`) as the underlying KEM.

use classic_mceliece_rust::{decapsulate_boxed, encapsulate_boxed};

use crate::psq_traits::*;

/// A code-based KEM based on the McEliece cryptosystem.
pub struct ClassicMcEliece;

/// Wrapper around `classic-mceliece-rust` encapsulation keys.
pub struct ClassicMcEliecePSQEncapsKey<'a>(classic_mceliece_rust::PublicKey<'a>);

impl Encode for ClassicMcEliecePSQEncapsKey<'_> {
    fn encode(&self) -> Vec<u8> {
        self.0.as_ref().to_vec()
    }
}

/// Wrapper around `classic-mceliece-rust` decapsulation keys.
pub struct ClassicMcEliecePSQDecapsKey<'a>(classic_mceliece_rust::SecretKey<'a>);

/// Wrapper around `classic-mceliece-rust` shared secrets.
pub struct ClassicMcEliecePSQSharedSecret<'a>(classic_mceliece_rust::SharedSecret<'a>);

impl Encode for ClassicMcEliecePSQSharedSecret<'_> {
    fn encode(&self) -> Vec<u8> {
        self.0.as_ref().to_vec()
    }
}

/// Wrapper around `classic-mceliece-rust` ciphertexts.
pub struct ClassicMcEliecePSQCiphertext(classic_mceliece_rust::Ciphertext);
impl Encode for ClassicMcEliecePSQCiphertext {
    fn encode(&self) -> Vec<u8> {
        self.0.as_ref().to_vec()
    }
}

impl private::Seal for ClassicMcEliece {}

impl<'t> crate::psq_traits::KEM<'t> for ClassicMcEliece {
    type Ciphertext = ClassicMcEliecePSQCiphertext;
    type SharedSecret = ClassicMcEliecePSQSharedSecret<'t>;
    type EncapsulationKey = ClassicMcEliecePSQEncapsKey<'t>;
    type DecapsulationKey = ClassicMcEliecePSQDecapsKey<'t>;

    fn encapsulate(
        ek: &Self::EncapsulationKey,
        rng: &mut (impl rand::CryptoRng + rand::Rng),
    ) -> Result<(Self::SharedSecret, Self::Ciphertext), crate::Error> {
        let (enc, ss) = encapsulate_boxed(&ek.0, rng);
        Ok((
            ClassicMcEliecePSQSharedSecret(ss),
            ClassicMcEliecePSQCiphertext(enc),
        ))
    }

    fn decapsulate(
        dk: &Self::DecapsulationKey,
        ctxt: &Self::Ciphertext,
    ) -> Result<Self::SharedSecret, crate::Error> {
        let ss = decapsulate_boxed(&ctxt.0, &dk.0);
        Ok(ClassicMcEliecePSQSharedSecret(ss))
    }
}

impl<'t> PSQ<'t> for ClassicMcEliece {
    type InnerKEM = Self;

    fn generate_key_pair(
        rng: &mut (impl rand::CryptoRng + rand::Rng),
    ) -> Result<
        (
            <Self::InnerKEM as KEM<'t>>::DecapsulationKey,
            <Self::InnerKEM as KEM<'t>>::EncapsulationKey,
        ),
        crate::Error,
    > {
        let (pk, sk) = classic_mceliece_rust::keypair_boxed(rng);
        Ok((
            ClassicMcEliecePSQDecapsKey(sk),
            ClassicMcEliecePSQEncapsKey(pk),
        ))
    }
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
