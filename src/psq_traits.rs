use rand::{CryptoRng, Rng};

use crate::Error;

const PRE_PSK_LENGTH: usize = 32;
const K0_LENGTH: usize = 32;
const KM_LENGTH: usize = 32;

const CONFIRMATION_CONTEXT: &[u8] = b"Confirmation";
const PSK_CONTEXT: &[u8] = b"PSK";
const MAC_INPUT: &[u8] = b"MAC-Input";

const MAC_LENGTH: usize = 32;
type Mac = [u8; MAC_LENGTH];

pub type PrePsk = [u8; PRE_PSK_LENGTH];
pub type PSQCiphertext = Vec<u8>;

pub(crate) mod private {
    pub trait Seal {}
}

pub trait Encode {
    fn encode(&self) -> Vec<u8>;
}

pub trait InnerKEM<'t>: private::Seal {
    type Ciphertext: Encode;
    type SharedSecret: Encode;
    type PublicKey: Encode;
    type PrivateKey;

    fn encapsulate(
        ek: &Self::PublicKey,
        rng: &mut (impl CryptoRng + Rng),
    ) -> Result<(Self::SharedSecret, Self::Ciphertext), Error>;

    fn decapsulate(
        dk: &Self::PrivateKey,
        ctxt: &Self::Ciphertext,
    ) -> Result<Self::SharedSecret, Error>;
}

/// A PSQ key pair.
pub trait PSQ<'t> {
    type KEM: InnerKEM<'t>;

    fn generate_key_pair(
        rng: &mut (impl CryptoRng + Rng),
    ) -> Result<
        (
            <Self::KEM as InnerKEM<'t>>::PrivateKey,
            <Self::KEM as InnerKEM<'t>>::PublicKey,
        ),
        Error,
    >;

    /// Generate a fresh PSQ component, and a message encapsulating it for the
    /// receiver.
    fn gen_pq_psk(
        pk: &<Self::KEM as InnerKEM<'t>>::PublicKey,
        sctx: &[u8],
        rng: &mut (impl CryptoRng + Rng),
    ) -> Result<(PrePsk, Ciphertext<'t, Self::KEM>), Error> {
        let (ikm, enc) = Self::KEM::encapsulate(pk, rng).map_err(|_| Error::PSQGenerationError)?;

        let k0 = compute_k0(&pk.encode(), &ikm.encode(), &enc.encode(), sctx)?;
        let mac = compute_mac(&k0)?;
        let psk = compute_psk(&k0)?;

        Ok((
            psk,
            Ciphertext {
                inner_ctxt: enc,
                mac,
            },
        ))
    }

    /// Derive a PSQ component from a PSQ component message.
    ///
    /// Can error, if the given PSQ message is cryptographically invalid.
    fn derive_pq_psk(
        sk: &<Self::KEM as InnerKEM<'t>>::PrivateKey,
        pk: &<Self::KEM as InnerKEM<'t>>::PublicKey,
        enc: &Ciphertext<'t, Self::KEM>,
        sctx: &[u8],
    ) -> Result<PrePsk, Error> {
        let Ciphertext { inner_ctxt, mac } = enc;

        let ik = Self::KEM::decapsulate(sk, &inner_ctxt).map_err(|_| Error::PSQDerivationError)?;

        let k0 = compute_k0(&pk.encode(), &ik.encode(), &inner_ctxt.encode(), sctx)?;
        let recomputed_mac = compute_mac(&k0)?;

        if compare(&recomputed_mac, mac) == 0 {
            let psk = compute_psk(&k0)?;
            Ok(psk)
        } else {
            Err(Error::PSQDerivationError)
        }
    }
}

/// A PSQ ciphertext, including MAC.
pub struct Ciphertext<'a, T: InnerKEM<'a>> {
    inner_ctxt: T::Ciphertext,
    mac: Mac,
}

impl<'a, T: InnerKEM<'a>> Ciphertext<'a, T> {
    pub(crate) fn serialize(&self) -> Vec<u8> {
        let mut serialized = self.inner_ctxt.encode();
        serialized.extend_from_slice(&self.mac);
        serialized
    }
}

/// PSQ public key trait.
pub trait PSQPublicKey<'t> {
    type KEM: InnerKEM<'t>;
}

pub trait PSQPrivateKey<'a, PK: PSQPublicKey<'a>> {}

/// Return 1 if `value` is not zero and 0 otherwise.
fn inz(value: u8) -> u8 {
    let value = value as u16;
    let result = ((value | (!value).wrapping_add(1)) >> 8) & 1;
    result as u8
}

#[inline(never)] // Don't inline this to avoid that the compiler optimizes this out.
fn is_non_zero(value: u8) -> u8 {
    core::hint::black_box(inz(value))
}

/// Best-effort constant time comparison.
fn compare(lhs: &[u8], rhs: &[u8]) -> u8 {
    let mut r: u8 = 0;
    for i in 0..lhs.len() {
        r |= lhs[i] ^ rhs[i];
    }

    is_non_zero(r)
}

fn compute_psk(k0: &[u8]) -> Result<PrePsk, Error> {
    let psk: PrePsk = libcrux_hkdf::expand(
        libcrux_hkdf::Algorithm::Sha256,
        k0,
        PSK_CONTEXT,
        PRE_PSK_LENGTH,
    )
    .map_err(|_| Error::PSQGenerationError)?
    .try_into()
    .expect("should receive the correct number of bytes from HKDF");
    Ok(psk)
}

fn compute_k0(pqpk: &[u8], ikm: &[u8], enc: &[u8], sctx: &[u8]) -> Result<Vec<u8>, Error> {
    let mut info = Vec::from(pqpk);
    info.extend_from_slice(&enc);
    info.extend_from_slice(sctx);

    let k0 = libcrux_hkdf::expand(libcrux_hkdf::Algorithm::Sha256, ikm, info, K0_LENGTH)
        .map_err(|_| Error::PSQDerivationError)?;

    Ok(k0)
}

fn compute_mac(k0: &[u8]) -> Result<Mac, Error> {
    let km = libcrux_hkdf::expand(
        libcrux_hkdf::Algorithm::Sha256,
        k0,
        CONFIRMATION_CONTEXT,
        KM_LENGTH,
    )
    .map_err(|_| Error::PSQGenerationError)?;

    let mac: Mac = libcrux_hmac::hmac(
        libcrux_hmac::Algorithm::Sha256,
        &km,
        MAC_INPUT,
        Some(MAC_LENGTH),
    )
    .try_into()
    .expect("should receive the correct number of bytes from HMAC");

    Ok(mac)
}
