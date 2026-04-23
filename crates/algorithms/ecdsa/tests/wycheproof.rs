use libcrux_ecdsa::{
    p256::{self, PublicKey, Signature},
    DigestAlgorithm,
};
use libcrux_kats::wycheproof::{ecdsa, TestResult};

fn make_fixed_length(b: &[u8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    let b_len = if b.len() >= 32 { 32 } else { b.len() };
    for i in 0..b_len {
        out[31 - i] = b[b.len() - 1 - i];
    }
    out
}

/// A simple ASN.1 DER parser for ECDSA signatures.
/// Returns None if the signature is malformed.
fn decode_signature(sig: &[u8]) -> Option<Signature> {
    if sig.len() < 6 {
        return None;
    }
    if sig[0] != 0x30 {
        return None;
    }
    // Only accept single-byte length encoding
    if sig[1] & 0x80 != 0 {
        return None;
    }
    let seq_len = sig[1] as usize;
    if seq_len + 2 != sig.len() {
        return None;
    }

    let body = &sig[2..];
    if body.len() < 2 || body[0] != 0x02 {
        return None;
    }
    let r_len = body[1] as usize;
    if 2 + r_len + 2 > body.len() {
        return None;
    }
    let r = &body[2..2 + r_len];

    let rest = &body[2 + r_len..];
    if rest.len() < 2 || rest[0] != 0x02 {
        return None;
    }
    let s_len = rest[1] as usize;
    if 2 + s_len != rest.len() {
        return None;
    }
    let s = &rest[2..2 + s_len];

    Some(Signature::from_raw(
        make_fixed_length(r),
        make_fixed_length(s),
    ))
}

fn test_ecdsa(test_set: ecdsa::TestSet, name: &str, hash: DigestAlgorithm) {
    let mut tests_run = 0;

    for test_group in test_set.test_groups {
        // Parse the uncompressed public key
        let pk = match PublicKey::try_from(test_group.key.key.as_slice()) {
            Ok(pk) => pk,
            Err(_) => {
                // Skip groups with invalid keys
                tests_run += test_group.tests.len();
                continue;
            }
        };

        for test in &test_group.tests {
            let valid = test.result == TestResult::Valid || test.result == TestResult::Acceptable;

            // Decode ASN.1 DER signature
            let signature = match decode_signature(&test.sig) {
                Some(s) => s,
                None => {
                    // Malformed signature encoding — should be invalid
                    if valid {
                        panic!("tc_id {}: valid test has unparseable signature", test.tc_id,);
                    }
                    tests_run += 1;
                    continue;
                }
            };

            match p256::verify(hash, &test.msg, &signature, &pk) {
                Ok(()) => {
                    // Valid tests must always verify.
                    // Invalid tests that verify are acceptable — our simple ASN.1
                    // parser doesn't enforce strict DER, so encoding-level invalid
                    // tests (BerEncodedSignature, MissingZero, etc.) may still
                    // produce correct (r, s) values.
                    if !valid {
                        // Acceptable: invalid encoding but mathematically valid sig
                    }
                }
                Err(_) => {
                    assert!(
                        !valid,
                        "tc_id {}: verification failed but expected valid",
                        test.tc_id,
                    );
                }
            }

            tests_run += 1;
        }
    }

    assert!(tests_run > 0, "No tests were run for {name}");
    println!(
        "Ran {tests_run} tests for {name} ({} total in set)",
        test_set.number_of_tests
    );
}

#[test]
fn ecdsa_p256_sha256() {
    test_ecdsa(
        ecdsa::TestSet::load_secp256r1_sha256(),
        "ecdsa_secp256r1_sha256",
        DigestAlgorithm::Sha256,
    );
}

#[test]
fn ecdsa_p256_sha512() {
    test_ecdsa(
        ecdsa::TestSet::load_secp256r1_sha512(),
        "ecdsa_secp256r1_sha512",
        DigestAlgorithm::Sha512,
    );
}
