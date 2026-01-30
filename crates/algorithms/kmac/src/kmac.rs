//! KMAC
//!
//! This crate implements KMAC.
#![no_std]

mod internals {
    pub(super) mod kmac;
}
use internals::kmac::*;
use libcrux_sha3::portable::incremental::{CShake128It, CShake256It};

pub fn kmac_128<'a>(tag: &'a mut [u8], key: &[u8], data: &[u8], customization: &[u8]) -> &'a [u8] {
    // Assert that key is long enough, i.e. at least 128 bits
    compute_kmac::<168, CShake128It>(
        tag,
        tag.len(),
        key,
        key.len(),
        data,
        customization,
        customization.len(),
    )
}

pub fn kmac_256<'a>(tag: &'a mut [u8], key: &[u8], data: &[u8], customization: &[u8]) -> &'a [u8] {
    // Assert that key is long enough, i.e. at least 256 bits
    compute_kmac::<136, CShake256It>(
        tag,
        tag.len(),
        key,
        key.len(),
        data,
        customization,
        customization.len(),
    )
}
