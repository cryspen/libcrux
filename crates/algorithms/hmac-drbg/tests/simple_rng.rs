//! Integration tests for the `HmacDrbgRng` wrapper types.
//!
//! Requires the `rand` feature (but NOT `health-tests`).  Run with:
//! ```text
//! cargo test -p libcrux-drbg --features rand --test simple_rng
//! ```
#![cfg(all(feature = "rand", not(feature = "health-tests")))]

use libcrux_hmac_drbg::{
    HmacSha256DrbgRng, HmacSha384DrbgRng, HmacSha512DrbgRng, MAX_GENERATE_BYTES,
};
use rand::{rand_core::UnwrapErr, rngs::SysRng, CryptoRng, Rng};

type OsRng = UnwrapErr<SysRng>;

fn make_sha256() -> HmacSha256DrbgRng<OsRng> {
    HmacSha256DrbgRng::new(UnwrapErr(SysRng), &[0u8; 32])
}

fn make_sha384() -> HmacSha384DrbgRng<OsRng> {
    HmacSha384DrbgRng::new(UnwrapErr(SysRng), &[0u8; 32])
}

fn make_sha512() -> HmacSha512DrbgRng<OsRng> {
    HmacSha512DrbgRng::new(UnwrapErr(SysRng), &[0u8; 32])
}

// ---------------------------------------------------------------------------
// SHA-256
// ---------------------------------------------------------------------------

#[test]
fn sha256_generates_non_zero_output() {
    let mut rng = make_sha256();
    let mut buf = [0u8; 64];
    rng.fill_bytes(&mut buf);
    assert_ne!(buf, [0u8; 64]);
}

#[test]
fn sha256_two_calls_produce_different_output() {
    let mut rng = make_sha256();
    let mut a = [0u8; 64];
    let mut b = [0u8; 64];
    rng.fill_bytes(&mut a);
    rng.fill_bytes(&mut b);
    assert_ne!(a, b);
}

#[test]
fn sha256_two_instances_differ() {
    let mut rng_a = make_sha256();
    let mut rng_b = make_sha256();
    let mut a = [0u8; 64];
    let mut b = [0u8; 64];
    rng_a.fill_bytes(&mut a);
    rng_b.fill_bytes(&mut b);
    assert_ne!(a, b);
}

#[test]
fn sha256_satisfies_crypto_rng() {
    fn need_crypto<R: CryptoRng>(rng: &mut R) -> u64 {
        rng.next_u64()
    }
    let mut rng = make_sha256();
    need_crypto(&mut rng);
}

// ---------------------------------------------------------------------------
// SHA-384
// ---------------------------------------------------------------------------

#[test]
fn sha384_generates_non_zero_output() {
    let mut rng = make_sha384();
    let mut buf = [0u8; 64];
    rng.fill_bytes(&mut buf);
    assert_ne!(buf, [0u8; 64]);
}

#[test]
fn sha384_two_calls_produce_different_output() {
    let mut rng = make_sha384();
    let mut a = [0u8; 64];
    let mut b = [0u8; 64];
    rng.fill_bytes(&mut a);
    rng.fill_bytes(&mut b);
    assert_ne!(a, b);
}

#[test]
fn sha384_two_instances_differ() {
    let mut rng_a = make_sha384();
    let mut rng_b = make_sha384();
    let mut a = [0u8; 64];
    let mut b = [0u8; 64];
    rng_a.fill_bytes(&mut a);
    rng_b.fill_bytes(&mut b);
    assert_ne!(a, b);
}

#[test]
fn sha384_satisfies_crypto_rng() {
    fn need_crypto<R: CryptoRng>(rng: &mut R) -> u64 {
        rng.next_u64()
    }
    let mut rng = make_sha384();
    need_crypto(&mut rng);
}

// ---------------------------------------------------------------------------
// SHA-512
// ---------------------------------------------------------------------------

#[test]
fn sha512_generates_non_zero_output() {
    let mut rng = make_sha512();
    let mut buf = [0u8; 64];
    rng.fill_bytes(&mut buf);
    assert_ne!(buf, [0u8; 64]);
}

#[test]
fn sha512_two_calls_produce_different_output() {
    let mut rng = make_sha512();
    let mut a = [0u8; 64];
    let mut b = [0u8; 64];
    rng.fill_bytes(&mut a);
    rng.fill_bytes(&mut b);
    assert_ne!(a, b);
}

#[test]
fn sha512_two_instances_differ() {
    let mut rng_a = make_sha512();
    let mut rng_b = make_sha512();
    let mut a = [0u8; 64];
    let mut b = [0u8; 64];
    rng_a.fill_bytes(&mut a);
    rng_b.fill_bytes(&mut b);
    assert_ne!(a, b);
}

#[test]
fn sha512_satisfies_crypto_rng() {
    fn need_crypto<R: CryptoRng>(rng: &mut R) -> u64 {
        rng.next_u64()
    }
    let mut rng = make_sha512();
    need_crypto(&mut rng);
}

/// Regression test for <https://github.com/celabshq/libcrux/issues/1556>
#[test]
#[should_panic(expected = "internal error: entered unreachable code")]
fn sha256_fill_bytes_panics() {
    let mut rng = make_sha256();
    for len in [0, MAX_GENERATE_BYTES, 2 * MAX_GENERATE_BYTES] {
        let mut output = vec![0xaa; len];
        rng.fill_bytes(&mut output);
        // assert for an empty vec would be true, but we still want to
        // execute fill_bytes to check that it doesn't panic
        if len != 0 {
            assert!(!output.iter().all(|b| *b == 0xaa))
        }
    }
}

/// Regression test for <https://github.com/celabshq/libcrux/issues/1556>
#[test]
#[should_panic(expected = "internal error: entered unreachable code")]
fn sha384_fill_bytes_panics() {
    let mut rng = make_sha384();
    for len in [0, MAX_GENERATE_BYTES, 2 * MAX_GENERATE_BYTES] {
        let mut output = vec![0xaa; len];
        rng.fill_bytes(&mut output);
        if len != 0 {
            assert!(!output.iter().all(|b| *b == 0xaa))
        }
    }
}

/// Regression test for <https://github.com/celabshq/libcrux/issues/1556>
#[test]
#[should_panic(expected = "internal error: entered unreachable code")]
fn sha512_fill_bytes_panics() {
    let mut rng = make_sha512();
    for len in [0, MAX_GENERATE_BYTES, 2 * MAX_GENERATE_BYTES] {
        let mut output = vec![0xaa; len];
        rng.fill_bytes(&mut output);
        if len != 0 {
            assert!(!output.iter().all(|b| *b == 0xaa))
        }
    }
}
