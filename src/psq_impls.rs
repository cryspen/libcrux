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

/// A PSQ public key
pub struct LibcruxPSQPublicKey(libcrux_kem::PublicKey);

impl Encode for LibcruxPSQPublicKey {
    fn encode(&self) -> Vec<u8> {
        self.0.encode()
    }
}

/// A PSQ private key
pub struct LibcruxPSQPrivateKey(libcrux_kem::PrivateKey);

pub struct LibcruxPSQCiphertext(libcrux_kem::Ct);

impl Encode for LibcruxPSQCiphertext {
    fn encode(&self) -> Vec<u8> {
        self.0.encode()
    }
}

pub struct LibcruxPSQSharedSecret(libcrux_kem::Ss);

impl Encode for LibcruxPSQSharedSecret {
    fn encode(&self) -> Vec<u8> {
        self.0.encode()
    }
}

trait LibcruxKEM: private::Seal {
    fn algorithm() -> libcrux_kem::Algorithm;
}

impl<T> crate::psq_traits::InnerKEM<'_> for T
where
    T: LibcruxKEM,
{
    type Ciphertext = LibcruxPSQCiphertext;
    type PublicKey = LibcruxPSQPublicKey;
    type PrivateKey = LibcruxPSQPrivateKey;
    type SharedSecret = LibcruxPSQSharedSecret;

    fn encapsulate(
        ek: &Self::PublicKey,
        rng: &mut (impl rand::CryptoRng + rand::Rng),
    ) -> Result<(Self::SharedSecret, Self::Ciphertext), crate::Error> {
        let (ss, enc) = ek.0.encapsulate(rng)?;
        Ok((LibcruxPSQSharedSecret(ss), LibcruxPSQCiphertext(enc)))
    }

    fn decapsulate(
        dk: &Self::PrivateKey,
        ctxt: &Self::Ciphertext,
    ) -> Result<Self::SharedSecret, crate::Error> {
        let ss = ctxt.0.decapsulate(&dk.0)?;
        Ok(LibcruxPSQSharedSecret(ss))
    }
}

impl<T: LibcruxKEM> crate::psq_traits::PSQ<'_> for T {
    type KEM = Self;

    fn generate_key_pair(
        rng: &mut (impl rand::CryptoRng + rand::Rng),
    ) -> Result<
        (
            <Self::KEM as InnerKEM<'_>>::PrivateKey,
            <Self::KEM as InnerKEM<'_>>::PublicKey,
        ),
        crate::Error,
    > {
        let (sk, pk) = libcrux_kem::key_gen(Self::algorithm(), rng)?;
        Ok((LibcruxPSQPrivateKey(sk), LibcruxPSQPublicKey(pk)))
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
                let (psk_initiator, message) = $alg::gen_pq_psk(&pk, sctx, &mut rng).unwrap();

                let psk_responder = $alg::derive_pq_psk(&sk, &pk, &message, sctx).unwrap();
                assert_eq!(psk_initiator, psk_responder);
            }
        };
    }

    libcrux_test!(X25519);
    libcrux_test!(MlKem768);
    libcrux_test!(XWingKemDraft02);
}
