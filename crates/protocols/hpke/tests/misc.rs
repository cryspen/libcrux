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
// Previously, debug_assert!(len < 256) fired in debug builds and
// release builds had no check at all (u16 truncation was silent).
//
// FIXED: the debug_assert was removed and the u16::MAX check now
// properly rejects values > 65535 in all builds. Values in
// 256..=65535 are correctly accepted (within HKDF limits).
// ---------------------------------------------------------------
#[test]
fn l1_export_large_length_returns_error() {
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

    // 65536 overflows u16: properly returns error in all builds.
    let _ = context
        .export(b"exporter", 65536)
        .expect_err("export(65536) should fail (exceeds u16::MAX)");
}

#[test]
fn l1_export_256_now_accepted() {
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

    // 256 fits in u16 and is valid per the RFC (HKDF-SHA256 max = 8160).
    // Previously panicked in debug builds; now correctly accepted.
    let result = context.export(b"exporter", 256);
    assert!(result.is_ok(), "export(256) should succeed after fix");
    assert_eq!(result.unwrap().len(), 256);
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

// ---------------------------------------------------------------
// BUG 1  RustCrypto AEAD open rejects empty-plaintext ciphertexts
//
// The AEAD open function checked msg.len() <= tag_length instead
// of msg.len() < tag_length. When encrypting empty plaintext, the
// ciphertext is exactly tag_length bytes, so the <= check
// erroneously rejects it as AeadInvalidCiphertext.
//
// With the bug: seal(aad, b"") succeeds producing 16 bytes, but
// open(aad, &ctxt) fails with AeadInvalidCiphertext because
// 16 <= 16 is true.
//
// With the fix: open(aad, &ctxt) succeeds because 16 < 16 is false.
// ---------------------------------------------------------------
#[test]
fn bug1_aead_open_empty_plaintext_rustcrypto() {
    for aead in &[
        AeadAlgorithm::Aes128Gcm,
        AeadAlgorithm::Aes256Gcm,
        AeadAlgorithm::ChaCha20Poly1305,
    ] {
        let mut hpke_cfg = Hpke::<HpkeRustCrypto>::new(
            Mode::Base,
            KemAlgorithm::DhKem25519,
            KdfAlgorithm::HkdfSha256,
            *aead,
        );
        let (sk_r, pk_r) = hpke_cfg.generate_key_pair().unwrap().into_keys();

        // Encrypt empty plaintext via single-shot API.
        let (enc, ctxt) = hpke_cfg
            .seal(&pk_r, b"info", b"aad", b"", None, None, None)
            .expect("seal of empty plaintext should succeed");

        // The ciphertext should be exactly the tag (16 bytes).
        assert_eq!(
            ctxt.len(),
            16,
            "ciphertext of empty plaintext should be tag-only ({:?})",
            aead
        );

        // Decrypt: this failed before the fix with AeadInvalidCiphertext.
        let ptxt = hpke_cfg
            .open(&enc, &sk_r, b"info", b"aad", &ctxt, None, None, None)
            .expect("open of empty plaintext ciphertext should succeed");

        assert_eq!(ptxt, b"", "decrypted empty plaintext should be empty");

        // Also test via context API.
        let (enc, mut sender_ctx) = hpke_cfg
            .setup_sender(&pk_r, b"info", None, None, None)
            .unwrap();
        let mut receiver_ctx = hpke_cfg
            .setup_receiver(&enc, &sk_r, b"info", None, None, None)
            .unwrap();
        let ct = sender_ctx.seal(b"aad", b"").unwrap();
        let pt = receiver_ctx
            .open(b"aad", &ct)
            .expect("context open of empty plaintext should succeed");
        assert_eq!(pt, b"");
    }
}

// ---------------------------------------------------------------
// BUG 1 (Libcrux variant) — same empty-plaintext round-trip test
// ---------------------------------------------------------------
#[test]
fn bug1_aead_open_empty_plaintext_libcrux() {
    use hpke_rs_libcrux::HpkeLibcrux;
    for aead in &[
        AeadAlgorithm::Aes128Gcm,
        AeadAlgorithm::Aes256Gcm,
        AeadAlgorithm::ChaCha20Poly1305,
    ] {
        let mut hpke_cfg = Hpke::<HpkeLibcrux>::new(
            Mode::Base,
            KemAlgorithm::DhKem25519,
            KdfAlgorithm::HkdfSha256,
            *aead,
        );
        let (sk_r, pk_r) = hpke_cfg.generate_key_pair().unwrap().into_keys();
        let (enc, ctxt) = hpke_cfg
            .seal(&pk_r, b"info", b"aad", b"", None, None, None)
            .expect("seal of empty plaintext should succeed");
        assert_eq!(ctxt.len(), 16);
        let ptxt = hpke_cfg
            .open(&enc, &sk_r, b"info", b"aad", &ctxt, None, None, None)
            .expect("open of empty plaintext ciphertext should succeed");
        assert_eq!(ptxt, b"");
    }
}

// ---------------------------------------------------------------
// BUG 2  Libcrux AEAD open returned wrong error type
//
// When decryption fails due to authentication tag mismatch, the
// Libcrux provider returned CryptoLibraryError (mapping to
// HpkeError::CryptoError) instead of AeadOpenError (mapping to
// HpkeError::OpenError).
//
// With the bug: tampered ciphertext → HpkeError::CryptoError
// With the fix: tampered ciphertext → HpkeError::OpenError
// ---------------------------------------------------------------
#[test]
fn bug2_libcrux_aead_open_error_type() {
    use hpke_rs_libcrux::HpkeLibcrux;
    let mut hpke_cfg = Hpke::<HpkeLibcrux>::new(
        Mode::Base,
        KemAlgorithm::DhKem25519,
        KdfAlgorithm::HkdfSha256,
        AeadAlgorithm::ChaCha20Poly1305,
    );
    let (sk_r, pk_r) = hpke_cfg.generate_key_pair().unwrap().into_keys();
    let (enc, mut ctxt) = hpke_cfg
        .seal(&pk_r, b"info", b"aad", b"plaintext", None, None, None)
        .unwrap();

    // Tamper with the ciphertext to cause an authentication failure.
    ctxt[0] ^= 0xff;

    let err = hpke_cfg
        .open(&enc, &sk_r, b"info", b"aad", &ctxt, None, None, None)
        .expect_err("tampered ciphertext must fail");

    // Must be OpenError, not CryptoError.
    assert_eq!(
        err,
        hpke::HpkeError::OpenError,
        "Libcrux AEAD authentication failure must return OpenError, got {:?}",
        err
    );
}

// Verify RustCrypto also returns OpenError for comparison.
#[test]
fn bug2_rustcrypto_aead_open_error_type() {
    let mut hpke_cfg = Hpke::<HpkeRustCrypto>::new(
        Mode::Base,
        KemAlgorithm::DhKem25519,
        KdfAlgorithm::HkdfSha256,
        AeadAlgorithm::ChaCha20Poly1305,
    );
    let (sk_r, pk_r) = hpke_cfg.generate_key_pair().unwrap().into_keys();
    let (enc, mut ctxt) = hpke_cfg
        .seal(&pk_r, b"info", b"aad", b"plaintext", None, None, None)
        .unwrap();

    ctxt[0] ^= 0xff;

    let err = hpke_cfg
        .open(&enc, &sk_r, b"info", b"aad", &ctxt, None, None, None)
        .expect_err("tampered ciphertext must fail");

    assert_eq!(
        err,
        hpke::HpkeError::OpenError,
        "RustCrypto AEAD authentication failure must return OpenError, got {:?}",
        err
    );
}

// ---------------------------------------------------------------
// BUG 3  labeled_expand debug_assert was too strict
//
// The debug_assert!(len < 256) rejected valid export lengths
// >= 256 in debug builds. The RFC allows up to 255*Nh bytes.
// After the fix, the debug_assert is removed and the proper
// u16 overflow check handles the limit.
// ---------------------------------------------------------------
#[test]
fn bug3_export_length_256_works() {
    let mut hpke_cfg = Hpke::<HpkeRustCrypto>::new(
        Mode::Base,
        KemAlgorithm::DhKem25519,
        KdfAlgorithm::HkdfSha256,
        AeadAlgorithm::ChaCha20Poly1305,
    );
    let (sk_r, pk_r) = hpke_cfg.generate_key_pair().unwrap().into_keys();
    let (enc, sender_ctx) = hpke_cfg
        .setup_sender(&pk_r, b"info", None, None, None)
        .unwrap();
    let receiver_ctx = hpke_cfg
        .setup_receiver(&enc, &sk_r, b"info", None, None, None)
        .unwrap();

    // 256 bytes: valid per RFC (max for HKDF-SHA256 is 255*32 = 8160).
    // This panicked in debug builds before the fix.
    let s = sender_ctx
        .export(b"ctx", 256)
        .expect("export(256) should succeed");
    let r = receiver_ctx
        .export(b"ctx", 256)
        .expect("export(256) should succeed");
    assert_eq!(s, r);
    assert_eq!(s.len(), 256);
}

#[test]
fn bug3_export_length_8160_works() {
    // Max for HKDF-SHA256: 255 * 32 = 8160
    let mut hpke_cfg = Hpke::<HpkeRustCrypto>::new(
        Mode::Base,
        KemAlgorithm::DhKem25519,
        KdfAlgorithm::HkdfSha256,
        AeadAlgorithm::ChaCha20Poly1305,
    );
    let (sk_r, pk_r) = hpke_cfg.generate_key_pair().unwrap().into_keys();
    let (enc, sender_ctx) = hpke_cfg
        .setup_sender(&pk_r, b"info", None, None, None)
        .unwrap();
    let receiver_ctx = hpke_cfg
        .setup_receiver(&enc, &sk_r, b"info", None, None, None)
        .unwrap();

    let s = sender_ctx
        .export(b"ctx", 8160)
        .expect("export(8160) should succeed (255*Nh for SHA-256)");
    let r = receiver_ctx
        .export(b"ctx", 8160)
        .expect("export(8160) should succeed");
    assert_eq!(s, r);
    assert_eq!(s.len(), 8160);
}

#[test]
fn bug3_export_length_exceeding_hkdf_limit_fails() {
    // 8161 exceeds 255*32 = 8160, so HKDF-SHA256 should reject it.
    let mut hpke_cfg = Hpke::<HpkeRustCrypto>::new(
        Mode::Base,
        KemAlgorithm::DhKem25519,
        KdfAlgorithm::HkdfSha256,
        AeadAlgorithm::ChaCha20Poly1305,
    );
    let (_sk_r, pk_r) = hpke_cfg.generate_key_pair().unwrap().into_keys();
    let (_enc, ctx) = hpke_cfg
        .setup_sender(&pk_r, b"info", None, None, None)
        .unwrap();

    let result = ctx.export(b"ctx", 8161);
    assert!(
        result.is_err(),
        "export(8161) should fail (exceeds HKDF-SHA256 limit)"
    );
}
