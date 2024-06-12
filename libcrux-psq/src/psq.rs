//! # PQ-PSK establishment protocol
//!
//! This crate implements a post-quantum (PQ) pre-shared key (PSK) establishment
//! protocol.

use chrono::{DateTime, Duration, Utc};
use libcrux_hmac::hmac;
use rand::{CryptoRng, Rng};

pub const PSK_EXPIRATION: Duration = Duration::hours(2);
pub const PSK_LENGTH: usize = 32;
pub const K0_LENGTH: usize = 32;
pub const KM_LENGTH: usize = 32;
pub const MAC_LENGTH: usize = 32;

type Psk = [u8; PSK_LENGTH];
type Mac = [u8; MAC_LENGTH];

pub enum Error {
    GenerationError,
    DerivationError,
}

pub struct PskMessage {
    enc: libcrux_kem::Ct,
    ts: i64,
    mac: Mac,
}

pub fn generate_psk(
    pk_b: &[u8],
    sctx: &[u8],
    rng: &mut (impl CryptoRng + Rng),
) -> Result<(Psk, PskMessage), Error> {
    let pk = libcrux_kem::PublicKey::decode(libcrux_kem::Algorithm::X25519, pk_b)
        .map_err(|_| Error::GenerationError)?;

    let (ik, enc) = pk.encapsulate(rng).map_err(|_| Error::GenerationError)?;
    let mut info = pk_b.to_vec();
    info.extend_from_slice(&enc.encode());
    info.extend_from_slice(sctx);

    let k0 = libcrux_hkdf::expand(
        libcrux_hkdf::Algorithm::Sha256,
        ik.encode(),
        info,
        K0_LENGTH,
    )
    .map_err(|_| Error::GenerationError)?;

    let km = libcrux_hkdf::expand(
        libcrux_hkdf::Algorithm::Sha256,
        &k0,
        b"Confirmation",
        KM_LENGTH,
    )
    .map_err(|_| Error::GenerationError)?;

    let psk: Psk = libcrux_hkdf::expand(libcrux_hkdf::Algorithm::Sha256, &k0, b"PSK", PSK_LENGTH)
        .map_err(|_| Error::GenerationError)?
        .try_into()
        .expect("should receive the correct number of bytes from HKDF");

    let now = Utc::now();
    let ts = now.timestamp();

    let mac: Mac = hmac(
        libcrux_hmac::Algorithm::Sha256,
        &km,
        &ts.to_be_bytes(),
        Some(MAC_LENGTH),
    )
    .try_into()
    .expect("should receive the correct number of bytes from HMAC");

    Ok((psk, PskMessage { enc, ts, mac }))
}

pub fn derive_psk(
    pk_b: &[u8],
    sk: &libcrux_kem::PrivateKey,
    message: &PskMessage,
    sctx: &[u8],
) -> Result<Psk, Error> {
    let PskMessage { enc, ts, mac } = message;

    let received_ts = if let Some(time) = DateTime::from_timestamp(*ts, 0) {
        time
    } else {
        return Err(Error::DerivationError);
    };

    let now = Utc::now();
    if now.signed_duration_since(received_ts) >= PSK_EXPIRATION {
        return Err(Error::DerivationError);
    }

    let ik = enc.decapsulate(sk).map_err(|_| Error::DerivationError)?;

    let mut info = pk_b.to_vec();
    info.extend_from_slice(&enc.encode());
    info.extend_from_slice(sctx);

    let k0 = libcrux_hkdf::expand(
        libcrux_hkdf::Algorithm::Sha256,
        ik.encode(),
        info,
        K0_LENGTH,
    )
    .map_err(|_| Error::DerivationError)?;

    let km = libcrux_hkdf::expand(
        libcrux_hkdf::Algorithm::Sha256,
        &k0,
        b"Confirmation",
        KM_LENGTH,
    )
    .map_err(|_| Error::DerivationError)?;

    let recomputed_mac: Mac = hmac(
        libcrux_hmac::Algorithm::Sha256,
        &km,
        &ts.to_be_bytes(),
        Some(MAC_LENGTH),
    )
    .try_into()
    .expect("should receive the correct number of bytes from HMAC");

    if recomputed_mac != *mac {
        return Err(Error::DerivationError);
    }

    let psk: Psk = libcrux_hkdf::expand(libcrux_hkdf::Algorithm::Sha256, &k0, b"PSK", PSK_LENGTH)
        .map_err(|_| Error::DerivationError)?
        .try_into()
        .expect("should receive the correct number of bytes from HKDF");

    Ok(psk)
}
