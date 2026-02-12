//! Tests provided with the report, adapted for the changes.

extern crate hpke_rs as hpke;

use hpke::prelude::*;
use hpke_rs_crypto::types::{AeadAlgorithm, KdfAlgorithm, KemAlgorithm};
use hpke_rs_rust_crypto::HpkeRustCrypto;

// ---------------------------------------------------------------
// M-3  X25519 zero-check uses black_box instead of subtle
//
// Demonstrate that a known small-order X25519 public key is
// correctly rejected (the check works), but the mechanism relies
// on black_box rather than constant-time comparison.
//
// The 8 small-order points for Curve25519 (in LE byte encoding):
//   0, 1, {order-1 encodings}, etc.
// The all-zeros point is the simplest to use.
// ---------------------------------------------------------------
#[test]
fn m3_x25519_small_order_point_rejected() {
    let mut hpke_cfg = Hpke::<HpkeRustCrypto>::new(
        Mode::Base,
        KemAlgorithm::DhKem25519,
        KdfAlgorithm::HkdfSha256,
        AeadAlgorithm::ChaCha20Poly1305,
    );

    // All-zeros public key: this is a small-order point.
    // X25519 with any private key will produce the all-zeros
    // shared secret, which the code checks via black_box.
    let zero_pk = HpkePublicKey::new(vec![0u8; 32]);
    let result = hpke_cfg.seal(&zero_pk, b"info", b"aad", b"plaintext", None, None, None);
    assert!(
        result.is_err(),
        "seal() with all-zero X25519 public key must fail"
    );

    // Other known small-order points on Curve25519 (LE encoding).
    // Each should also produce the zero shared secret after
    // clamping and scalar multiplication.
    let small_order_points: Vec<[u8; 32]> = vec![
        // 0 (identity)
        [0u8; 32],
        // 1 (generator of the small subgroup of order 8)
        {
            let mut p = [0u8; 32];
            p[0] = 1;
            p
        },
        // p - 1  (where p = 2^255 - 19)
        {
            let mut p = [0xff; 32];
            // 2^255 - 19 - 1 = 2^255 - 20
            // In LE: 0xec, 0xff..ff, 0x7f
            p[0] = 0xec;
            p[31] = 0x7f;
            p
        },
        // p (= 0 mod p)
        {
            let mut p = [0xff; 32];
            p[0] = 0xed;
            p[31] = 0x7f;
            p
        },
    ];

    for point in &small_order_points {
        let pk = HpkePublicKey::new(point.to_vec());
        let r = hpke_cfg.seal(&pk, b"info", b"aad", b"plaintext", None, None, None);
        // These should be rejected. Some may not produce the
        // all-zero output (x25519-dalek may reject them at the
        // deserialization level), so we just verify no silent
        // success with a small-order key.
        if r.is_ok() {
            panic!(
                "seal() succeeded with small-order point {:02x?} \
                 — this may indicate a missing validation",
                point
            );
        }
    }
    // Finding M-3: the rejection *works* but uses black_box
    // instead of subtle::ConstantTimeEq. The timing guarantee
    // is not reliable.
}

// ---------------------------------------------------------------
// M-4  compute_nonce() panics on export-only contexts
//
// Construct an HPKE context with AeadAlgorithm::HpkeExport, then
// call seal().  The compute_nonce() subtraction underflows before
// the AEAD backend can reject the algorithm.
// ---------------------------------------------------------------
#[test]
fn m4_compute_nonce_panics_on_export_only_context() {
    let mut hpke_cfg = Hpke::<HpkeRustCrypto>::new(
        Mode::Base,
        KemAlgorithm::DhKem25519,
        KdfAlgorithm::HkdfSha256,
        AeadAlgorithm::HpkeExport, // nonce length = 0
    );
    let (_sk_r, pk_r) = hpke_cfg.generate_key_pair().unwrap().into_keys();

    let (_enc, mut context) = hpke_cfg
        .setup_sender(&pk_r, b"info", None, None, None)
        .unwrap();

    // This calls compute_nonce() which does:
    //   vec![0u8; self.nonce.len() - seq.len()]
    //          =  vec![0u8; 0 - 8]
    // Panics with arithmetic underflow in debug, wraps in release.
    context
        .seal(b"aad", b"plaintext")
        .expect_err("export only ciphersuite with seal");
}

// Verify that export() still works on an export-only context
// (the intended use-case).
#[test]
fn m4_export_only_context_export_works() {
    let mut hpke_cfg = Hpke::<HpkeRustCrypto>::new(
        Mode::Base,
        KemAlgorithm::DhKem25519,
        KdfAlgorithm::HkdfSha256,
        AeadAlgorithm::HpkeExport,
    );
    let (sk_r, pk_r) = hpke_cfg.generate_key_pair().unwrap().into_keys();

    let (enc, sender_ctx) = hpke_cfg
        .setup_sender(&pk_r, b"info", None, None, None)
        .unwrap();
    let receiver_ctx = hpke_cfg
        .setup_receiver(&enc, &sk_r, b"info", None, None, None)
        .unwrap();

    // export() does not call compute_nonce(), so it must work.
    let s = sender_ctx.export(b"ctx", 32).unwrap();
    let r = receiver_ctx.export(b"ctx", 32).unwrap();
    assert_eq!(s, r);
}

// ---------------------------------------------------------------
// L-1  labeled_expand silently truncates len from usize to u16
//
// In debug builds, debug_assert!(len < 256) fires as a panic.
// In release builds, the assert is stripped and the `len as u16`
// cast silently truncates, causing a wrong HKDF label encoding.
//
// This test demonstrates the debug_assert panic.  The real bug
// is that release builds have NO check at all — the truncation
// happens silently.  The fix is a hard check (not debug_assert).
// ---------------------------------------------------------------
#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "len < 256")]
fn l1_export_large_length_hits_debug_assert() {
    export_large_length_hits_debug_assert();
}

#[test]
#[cfg(not(debug_assertions))]
fn l1_export_large_length_hits_debug_assert() {
    export_large_length_hits_debug_assert();
}

fn export_large_length_hits_debug_assert() {
    // In debug builds this panics at the debug_assert in kdf.rs.
    // In release builds this would silently truncate `len as u16`.
    let mut hpke_cfg = Hpke::<HpkeRustCrypto>::new(
        Mode::Base,
        KemAlgorithm::DhKem25519,
        KdfAlgorithm::HkdfSha256,
        AeadAlgorithm::ChaCha20Poly1305,
    );
    let (_sk_r, pk_r) = hpke_cfg.generate_key_pair().unwrap().into_keys();
    let (_enc, context) = hpke_cfg
        .setup_sender(&pk_r, b"info", None, None, None)
        .unwrap();

    // 65536 overflows u16 to 0.
    // Debug: panics at debug_assert!(len < 256).
    // Release: silently encodes length=0 in the HKDF label.
    let _ = context
        .export(b"exporter", 65536)
        .expect_err("export only ciphersuite with seal");
}

// Demonstrate the debug_assert threshold is also wrong: the
// RFC uses a u16 length field, so values 256..=65535 should be
// valid, but debug_assert!(len < 256) rejects them.
#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "len < 256")]
fn l1_export_256_rejected_by_overly_strict_debug_assert() {
    export_256_rejected_by_overly_strict_debug_assert();
}

#[test]
#[cfg(not(debug_assertions))]
fn l1_export_256_rejected_by_overly_strict_debug_assert() {
    export_256_rejected_by_overly_strict_debug_assert();
}

fn export_256_rejected_by_overly_strict_debug_assert() {
    let mut hpke_cfg = Hpke::<HpkeRustCrypto>::new(
        Mode::Base,
        KemAlgorithm::DhKem25519,
        KdfAlgorithm::HkdfSha256,
        AeadAlgorithm::ChaCha20Poly1305,
    );
    let (_sk_r, pk_r) = hpke_cfg.generate_key_pair().unwrap().into_keys();
    let (_enc, context) = hpke_cfg
        .setup_sender(&pk_r, b"info", None, None, None)
        .unwrap();

    // 256 fits in u16 and is valid per the RFC, but
    // debug_assert!(len < 256) rejects it in debug builds.
    // HKDF-SHA256 max is 8160, so 256 is within HKDF limits too.
    let _ = context.export(b"exporter", 256);
}

// A value within the current (overly strict) limit works.
#[test]
fn l1_export_within_limits_works() {
    let mut hpke_cfg = Hpke::<HpkeRustCrypto>::new(
        Mode::Base,
        KemAlgorithm::DhKem25519,
        KdfAlgorithm::HkdfSha256,
        AeadAlgorithm::ChaCha20Poly1305,
    );
    let (_sk_r, pk_r) = hpke_cfg.generate_key_pair().unwrap().into_keys();
    let (_enc, context) = hpke_cfg
        .setup_sender(&pk_r, b"info", None, None, None)
        .unwrap();

    let result = context.export(b"exporter", 64);
    assert!(result.is_ok(), "export(64) should succeed");
}
