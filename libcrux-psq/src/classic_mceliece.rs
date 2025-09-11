//! PSQ implementation backed by `classic-mceliece-rust`
//!
//! This module implements PSQ using ClassicMcEliece (parameter set
//! `mceliece460896f`) as the underlying KEM.

use classic_mceliece_rust::{
    decapsulate_boxed, encapsulate_boxed, keypair_boxed, Ciphertext as Ct, PublicKey as Pk,
    SecretKey as Sk, SharedSecret as Ss,
};

use libcrux_traits::kem::{KEMError, KeyPair as KEMKeyPair, KEM};
use tls_codec::{Deserialize, Serialize, SerializeBytes, Size, VLByteSlice, VLBytes};

const MCELIECE460896F_CIPHERTEXT_LEN: usize = 156;

/// A wrapper around the `classic_mceliece_rust` type `Ciphertext`.
pub struct Ciphertext(pub(crate) Ct);
impl Serialize for Ciphertext {
    fn tls_serialize<W: std::io::Write>(&self, writer: &mut W) -> Result<usize, tls_codec::Error> {
        VLByteSlice(self.0.as_ref()).tls_serialize(writer)
    }
}

impl Deserialize for Ciphertext {
    fn tls_deserialize<R: std::io::Read>(bytes: &mut R) -> Result<Self, tls_codec::Error>
    where
        Self: Sized,
    {
        let bytes_deserialized = VLBytes::tls_deserialize(bytes)?;
        // XXX: This is the expected length of the ciphertext for mceliece460896f.
        // If we didn't want to hardcode this, we'd have to pull in `generic-array` as a dependency and do something like
        // ```
        // let array = GenericArray<u8, Ciphertext::EncappedKeySize>::from(bytes_deserialized);
        // let ciphertext =  Ciphertext::from_bytes(&array)?;
        // ```
        Ok(Ciphertext(Ct::from(
            <[u8; MCELIECE460896F_CIPHERTEXT_LEN]>::try_from(bytes_deserialized.as_slice())?,
        )))
    }
}

impl Size for Ciphertext {
    fn tls_serialized_len(&self) -> usize {
        VLByteSlice(self.0.as_ref()).tls_serialized_len()
    }
}

/// A wrapper around the `classic_mceliece_rust` type `PublicKey`.
pub struct PublicKey(pub(crate) Pk<'static>);

/// A wrapper around the `classic_mceliece_rust` type `SecretKey`.
pub struct SecretKey(pub(crate) Sk<'static>);

/// A key pair wrapper type.
pub struct KeyPair {
    /// Public key
    pub pk: PublicKey,
    pub(crate) sk: SecretKey,
}

impl KeyPair {
    /// Generate a new key pair.
    pub fn generate_key_pair(rng: &mut impl rand::CryptoRng) -> Self {
        let mut rng = McElieceRng::new(rng);
        let (pk, sk) = keypair_boxed(&mut rng);
        Self {
            pk: PublicKey(pk),
            sk: SecretKey(sk),
        }
    }
}

impl Size for PublicKey {
    fn tls_serialized_len(&self) -> usize {
        VLByteSlice(self.0.as_ref()).tls_serialized_len()
    }
}
impl Serialize for PublicKey {
    fn tls_serialize<W: std::io::Write>(&self, writer: &mut W) -> Result<usize, tls_codec::Error> {
        VLByteSlice(self.0.as_ref()).tls_serialize(writer)
    }
}
impl<'a> Serialize for &'a PublicKey {
    fn tls_serialize<W: std::io::Write>(&self, writer: &mut W) -> Result<usize, tls_codec::Error> {
        VLByteSlice(self.0.as_ref()).tls_serialize(writer)
    }
}

impl<'a> Size for &'a PublicKey {
    fn tls_serialized_len(&self) -> usize {
        VLByteSlice(self.0.as_ref()).tls_serialized_len()
    }
}
impl<'a> Size for SharedSecret<'a> {
    fn tls_serialized_len(&self) -> usize {
        VLByteSlice(self.0.as_ref()).tls_serialized_len()
    }
}

impl<'a> SerializeBytes for SharedSecret<'a> {
    fn tls_serialize(&self) -> Result<Vec<u8>, tls_codec::Error> {
        SerializeBytes::tls_serialize(&self.0.as_ref())
    }
}

/// A wrapper around the `classic_mceliece_rust` type `SharedSecret`.
pub struct SharedSecret<'a>(pub(crate) Ss<'a>);

impl<'a> Serialize for SharedSecret<'a> {
    fn tls_serialize<W: std::io::Write>(&self, writer: &mut W) -> Result<usize, tls_codec::Error> {
        VLByteSlice(self.0.as_ref()).tls_serialize(writer)
    }
}

/// A code-based KEM based on the McEliece cryptosystem.
pub struct ClassicMcEliece;

#[cfg(feature = "legacy")]
impl crate::legacy::traits::private::Seal for ClassicMcEliece {}

// This is only here because `classic-mceliece-rust` still depends on
// `rand` version `0.8.0`.
pub(crate) struct McElieceRng<'a, T: rand::CryptoRng> {
    inner_rng: &'a mut T,
}

impl<'a, T: rand::CryptoRng> McElieceRng<'a, T> {
    pub(crate) fn new(inner_rng: &'a mut T) -> Self {
        Self { inner_rng }
    }
}

impl<T: rand::CryptoRng> rand_old::RngCore for McElieceRng<'_, T> {
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
        self.inner_rng.fill_bytes(dest);
        Ok(())
    }
}

impl<T: rand::CryptoRng> rand_old::CryptoRng for McElieceRng<'_, T> {}

impl KEM for ClassicMcEliece {
    /// The KEM's ciphertext.
    type Ciphertext = Ciphertext;
    /// The KEM's shared secret.
    type SharedSecret = SharedSecret<'static>;
    /// The KEM's encapsulation key.
    type EncapsulationKey = PublicKey;
    /// The KEM's decapsulation key.
    type DecapsulationKey = Sk<'static>;

    /// Generate a pair of encapsulation and decapsulation keys.
    fn generate_key_pair(
        rng: &mut impl rand::CryptoRng,
    ) -> Result<KEMKeyPair<Sk<'static>, PublicKey>, KEMError> {
        let mut rng = McElieceRng::new(rng);
        let (pk, sk) = keypair_boxed(&mut rng);
        Ok((sk, PublicKey(pk)))
    }

    /// Encapsulate a shared secret towards a given encapsulation key.
    fn encapsulate(
        ek: &Self::EncapsulationKey,
        rng: &mut impl rand::CryptoRng,
    ) -> Result<(Self::SharedSecret, Self::Ciphertext), KEMError> {
        let mut rng = McElieceRng::new(rng);
        let (enc, ss) = encapsulate_boxed(&ek.0, &mut rng);
        Ok((SharedSecret(ss), Ciphertext(enc)))
    }

    /// Decapsulate a shared secret.
    fn decapsulate(
        dk: &Self::DecapsulationKey,
        ctxt: &Self::Ciphertext,
    ) -> Result<Self::SharedSecret, KEMError> {
        let ss = decapsulate_boxed(&ctxt.0, dk);
        Ok(SharedSecret(ss))
    }
}

#[cfg(feature = "legacy")]
impl crate::legacy::traits::PSQ for ClassicMcEliece {
    type InnerKEM = Self;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::legacy::traits::PSQ;

    #[test]
    #[cfg(feature = "legacy")]
    fn simple_classic_mceliece() {
        let mut rng = rand::rng();
        let (sk, pk) = ClassicMcEliece::generate_key_pair(&mut rng).unwrap();
        let sctx = b"test context";
        let (psk_initiator, message) =
            ClassicMcEliece::encapsulate_psq(&pk, sctx, &mut rng).unwrap();

        let psk_responder = ClassicMcEliece::decapsulate_psq(&sk, &pk, &message, sctx).unwrap();
        assert_eq!(psk_initiator, psk_responder);
    }
}
