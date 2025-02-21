//! This module provides common traits for PSQ implementations.
use libcrux_hkdf::{expand as hkdf_expand, Algorithm as HKDF_Algorithm};
use libcrux_hmac::{hmac, Algorithm as HMAC_Algorithm};
use libcrux_traits::kem::KEM;
use rand::{CryptoRng, Rng};

use crate::Error;

/// The length in bytes of the generated PSQ component.
pub const PSQ_COMPONENT_LENGTH: usize = 32;
const K0_LENGTH: usize = 32;
const KM_LENGTH: usize = 32;

const CONFIRMATION_CONTEXT: &[u8] = b"Confirmation";
const PSK_CONTEXT: &[u8] = b"PSK";
const MAC_INPUT: &[u8] = b"MAC-Input";

const MAC_LENGTH: usize = 32;
type Mac = [u8; MAC_LENGTH];

/// A post-quantum shared secret component.
pub type PSQComponent = [u8; PSQ_COMPONENT_LENGTH];

/// A common trait for encoding structures into byte vectors.
pub trait Encode {
    // TODO: This can only become proper `no_std` once we get slices
    // of the backing datastructure from `libcrux_kem`.
    // See: https://github.com/cryspen/libcrux/issues/817
    /// Encodes self into a byte vector.
    ///
    /// This encoding needs to be unique.
    fn encode(&self) -> Vec<u8>;
}

pub(crate) mod private {
    pub trait Seal {}
}
/// This trait provides the interface for encapsulating a PSQ
/// component using an underlying KEM.
pub trait PSQ: private::Seal {
    /// The underlying KEM.
    type InnerKEM: KEM<Ciphertext: Encode, SharedSecret: Encode, EncapsulationKey: Encode>;

    /// Encapsulate a fresh PSQ component.
    fn encapsulate_psq(
        pk: &<Self::InnerKEM as KEM>::EncapsulationKey,
        sctx: &[u8],
        rng: &mut (impl CryptoRng + Rng),
    ) -> Result<(PSQComponent, Ciphertext<Self::InnerKEM>), Error> {
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
        sk: &<Self::InnerKEM as KEM>::DecapsulationKey,
        pk: &<Self::InnerKEM as KEM>::EncapsulationKey,
        enc: &Ciphertext<Self::InnerKEM>,
        sctx: &[u8],
    ) -> Result<PSQComponent, Error> {
        let Ciphertext { inner_ctxt, mac } = enc;

        let ik =
            Self::InnerKEM::decapsulate(sk, inner_ctxt).map_err(|_| Error::PSQDerivationError)?;

        let k0 = compute_k0(&pk.encode(), &ik.encode(), &inner_ctxt.encode(), sctx)?;
        let recomputed_mac = compute_mac(&k0)?;

        if compare(&recomputed_mac, mac) == 0 {
            compute_psk(&k0)
        } else {
            Err(Error::PSQDerivationError)
        }
    }
}

/// A PSQ ciphertext, including MAC.
pub struct Ciphertext<T: KEM> {
    inner_ctxt: T::Ciphertext,
    mac: Mac,
}

impl<T: KEM<Ciphertext: Encode>> Encode for Ciphertext<T> {
    fn encode(&self) -> Vec<u8> {
        let mut serialized = self.inner_ctxt.encode();
        serialized.extend_from_slice(&self.mac);
        serialized
    }
}

// TODO: Use functions from `secrets` crate instead once that's merged.
// See:
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

// TODO: This will not be `no_std` until we have incremental HKDF.
// See: https://github.com/cryspen/libcrux/issues/767
//      https://github.com/cryspen/libcrux/issues/820
fn compute_psk(k0: &[u8]) -> Result<PSQComponent, Error> {
    let psk: PSQComponent = hkdf_expand(
        HKDF_Algorithm::Sha256,
        k0,
        PSK_CONTEXT,
        PSQ_COMPONENT_LENGTH,
    )
    .map_err(|_| Error::PSQGenerationError)?
    .try_into()
    .expect("should receive the correct number of bytes from HKDF");
    Ok(psk)
}

// TODO: This will not be `no_std` until we have incremental HKDF.
// See: https://github.com/cryspen/libcrux/issues/816
fn compute_k0(pqpk: &[u8], ikm: &[u8], enc: &[u8], sctx: &[u8]) -> Result<Vec<u8>, Error> {
    let mut info = Vec::from(pqpk);
    info.extend_from_slice(enc);
    info.extend_from_slice(sctx);

    let k0 = hkdf_expand(HKDF_Algorithm::Sha256, ikm, info, K0_LENGTH)
        .map_err(|_| Error::PSQDerivationError)?;

    Ok(k0)
}

// TODO: This will not be `no_std` until we have incremental HKDF.
// See: https://github.com/cryspen/libcrux/issues/816
fn compute_mac(k0: &[u8]) -> Result<Mac, Error> {
    let km = hkdf_expand(HKDF_Algorithm::Sha256, k0, CONFIRMATION_CONTEXT, KM_LENGTH)
        .map_err(|_| Error::PSQGenerationError)?;

    let mac: Mac = hmac(HMAC_Algorithm::Sha256, &km, MAC_INPUT, Some(MAC_LENGTH))
        .try_into()
        .expect("should receive the correct number of bytes from HMAC");

    Ok(mac)
}
