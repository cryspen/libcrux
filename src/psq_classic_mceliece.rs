use classic_mceliece_rust::{decapsulate_boxed, encapsulate_boxed};

use crate::psq_traits::*;

pub struct ClassicMcEliece;

pub struct ClassicMcEliecePSQPublicKey<'a>(classic_mceliece_rust::PublicKey<'a>);
impl<'a> Encode for ClassicMcEliecePSQPublicKey<'a> {
    fn encode(&self) -> Vec<u8> {
        self.0.as_ref().to_vec()
    }
}

pub struct ClassicMcEliecePSQPrivateKey<'a>(classic_mceliece_rust::SecretKey<'a>);

pub struct ClassicMcEliecePSQSharedSecret<'a>(classic_mceliece_rust::SharedSecret<'a>);
impl<'a> Encode for ClassicMcEliecePSQSharedSecret<'a> {
    fn encode(&self) -> Vec<u8> {
        self.0.as_ref().to_vec()
    }
}

pub struct ClassicMcEliecePSQCiphertext(classic_mceliece_rust::Ciphertext);
impl Encode for ClassicMcEliecePSQCiphertext {
    fn encode(&self) -> Vec<u8> {
        self.0.as_ref().to_vec()
    }
}

impl private::Seal for ClassicMcEliece {}

impl<'t> crate::psq_traits::InnerKEM<'t> for ClassicMcEliece {
    type Ciphertext = ClassicMcEliecePSQCiphertext;
    type SharedSecret = ClassicMcEliecePSQSharedSecret<'t>;
    type PublicKey = ClassicMcEliecePSQPublicKey<'t>;
    type PrivateKey = ClassicMcEliecePSQPrivateKey<'t>;

    fn encapsulate(
        ek: &Self::PublicKey,
        rng: &mut (impl rand::CryptoRng + rand::Rng),
    ) -> Result<(Self::SharedSecret, Self::Ciphertext), crate::Error> {
        let (enc, ss) = encapsulate_boxed(&ek.0, rng);
        Ok((
            ClassicMcEliecePSQSharedSecret(ss),
            ClassicMcEliecePSQCiphertext(enc),
        ))
    }

    fn decapsulate(
        dk: &Self::PrivateKey,
        ctxt: &Self::Ciphertext,
    ) -> Result<Self::SharedSecret, crate::Error> {
        let ss = decapsulate_boxed(&ctxt.0, &dk.0);
        Ok(ClassicMcEliecePSQSharedSecret(ss))
    }
}

impl<'t> PSQ<'t> for ClassicMcEliece {
    type KEM = Self;

    fn generate_key_pair(
        rng: &mut (impl rand::CryptoRng + rand::Rng),
    ) -> Result<
        (
            <Self::KEM as InnerKEM<'t>>::PrivateKey,
            <Self::KEM as InnerKEM<'t>>::PublicKey,
        ),
        crate::Error,
    > {
        let (pk, sk) = classic_mceliece_rust::keypair_boxed(rng);
        Ok((
            ClassicMcEliecePSQPrivateKey(sk),
            ClassicMcEliecePSQPublicKey(pk),
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
        let (psk_initiator, message) = ClassicMcEliece::gen_pq_psk(&pk, sctx, &mut rng).unwrap();

        let psk_responder = ClassicMcEliece::derive_pq_psk(&sk, &pk, message, sctx).unwrap();
        assert_eq!(psk_initiator, psk_responder);
    }
}
