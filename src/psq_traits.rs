//! This module provides common traits for PSQ implementations.
use rand::{CryptoRng, Rng};

use crate::Error;

const PSQ_COMPONENT_LENGTH: usize = 32;
const K0_LENGTH: usize = 32;
const KM_LENGTH: usize = 32;

const CONFIRMATION_CONTEXT: &[u8] = b"Confirmation";
const PSK_CONTEXT: &[u8] = b"PSK";
const MAC_INPUT: &[u8] = b"MAC-Input";

const MAC_LENGTH: usize = 32;
type Mac = [u8; MAC_LENGTH];

/// A post-quantum shared secret component.
pub type PSQComponent = [u8; PSQ_COMPONENT_LENGTH];

pub(crate) mod private {
    pub trait Seal {}
}

/// A common trait for encoding structures into byte vectors.
pub trait Encode {
    /// Encodes self into a byte vector.
    ///
    /// This encoding needs to be unique.
    fn encode(&self) -> Vec<u8>;
}

/// This trait captures the required interface of the underlying KEM
/// used to encapsulate a PSQ component.
pub trait KEM<'t>: private::Seal {
    /// The underlying KEM's ciphertext.
    type Ciphertext: Encode;
    /// The underlying KEM's shared secret.
    type SharedSecret: Encode;
    /// The underlying KEM's encapsulation key.
    type EncapsulationKey: Encode;
    /// The underlying KEM's decapsulation key.
    type DecapsulationKey;

    /// Encapsulate a shared secret towards a given encapsulation key.
    fn encapsulate(
        ek: &Self::EncapsulationKey,
        rng: &mut (impl CryptoRng + Rng),
    ) -> Result<(Self::SharedSecret, Self::Ciphertext), Error>;

    /// Decapsulate a shared secret.
    fn decapsulate(
        dk: &Self::DecapsulationKey,
        ctxt: &Self::Ciphertext,
    ) -> Result<Self::SharedSecret, Error>;
}

/// This trait provides the interface for encapsulating a PSQ
/// component using an underlying KEM.
pub trait PSQ<'t> {
    /// The underlying KEM.
    type InnerKEM: KEM<'t>;

    /// Generate a pair of encapsulation and decapsulation keys.
    fn generate_key_pair(
        rng: &mut (impl CryptoRng + Rng),
    ) -> Result<
        (
            <Self::InnerKEM as KEM<'t>>::DecapsulationKey,
            <Self::InnerKEM as KEM<'t>>::EncapsulationKey,
        ),
        Error,
    >;

    /// Encapsulate a fresh PSQ component.
    fn encapsulate_psq(
        pk: &<Self::InnerKEM as KEM<'t>>::EncapsulationKey,
        sctx: &[u8],
        rng: &mut (impl CryptoRng + Rng),
    ) -> Result<(PSQComponent, Ciphertext<'t, Self::InnerKEM>), Error> {
        let (ikm, enc) =
            Self::InnerKEM::encapsulate(pk, rng).map_err(|_| Error::PSQGenerationError)?;

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

    /// Decapsulate a PSQ component from a PSQ ciphertext.
    ///
    /// Can error, if the given PSQ message is cryptographically invalid.
    fn decapsulate_psq(
        sk: &<Self::InnerKEM as KEM<'t>>::DecapsulationKey,
        pk: &<Self::InnerKEM as KEM<'t>>::EncapsulationKey,
        enc: &Ciphertext<'t, Self::InnerKEM>,
        sctx: &[u8],
    ) -> Result<PSQComponent, Error> {
        let Ciphertext { inner_ctxt, mac } = enc;

        let ik =
            Self::InnerKEM::decapsulate(sk, inner_ctxt).map_err(|_| Error::PSQDerivationError)?;

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
pub struct Ciphertext<'a, T: KEM<'a>> {
    inner_ctxt: T::Ciphertext,
    mac: Mac,
}

impl<'a, T: KEM<'a>> Encode for Ciphertext<'a, T> {
    fn encode(&self) -> Vec<u8> {
        let mut serialized = self.inner_ctxt.encode();
        serialized.extend_from_slice(&self.mac);
        serialized
    }
}

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

fn compute_psk(k0: &[u8]) -> Result<PSQComponent, Error> {
    let psk: PSQComponent = libcrux_hkdf::expand(
        libcrux_hkdf::Algorithm::Sha256,
        k0,
        PSK_CONTEXT,
        PSQ_COMPONENT_LENGTH,
    )
    .map_err(|_| Error::PSQGenerationError)?
    .try_into()
    .expect("should receive the correct number of bytes from HKDF");
    Ok(psk)
}

fn compute_k0(pqpk: &[u8], ikm: &[u8], enc: &[u8], sctx: &[u8]) -> Result<Vec<u8>, Error> {
    let mut info = Vec::from(pqpk);
    info.extend_from_slice(enc);
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
