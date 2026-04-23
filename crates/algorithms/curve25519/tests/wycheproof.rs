use libcrux_kats::wycheproof::{xdh, TestResult};

#[test]
fn x25519() {
    let test_set = xdh::TestSet::load_x25519();
    let mut tests_run = 0;

    for test_group in test_set.test_groups {
        for test in &test_group.tests {
            if test.public.len() != 32 || test.private.len() != 32 {
                assert_eq!(test.result, TestResult::Invalid);
                tests_run += 1;
                continue;
            }

            let pk: [u8; 32] = test.public[..].try_into().unwrap();
            let sk: [u8; 32] = test.private[..].try_into().unwrap();
            let mut out = [0u8; 32];

            // HACL rejects some "acceptable" vectors that produce low-order
            // or twist points resulting in a zero shared secret.
            let hacl_rejects = test.flags.iter().any(|f| {
                matches!(
                    f.as_str(),
                    "LowOrderPublic" | "SmallPublicKey" | "ZeroSharedSecret"
                )
            });

            match libcrux_curve25519::ecdh(&mut out, &pk, &sk) {
                Ok(()) => {
                    assert_eq!(
                        &out[..],
                        test.shared.as_slice(),
                        "tc_id {}: shared secret mismatch",
                        test.tc_id,
                    );
                }
                Err(_) => {
                    assert!(
                        test.result == TestResult::Invalid || hacl_rejects,
                        "tc_id {}: unexpected error (result={:?}, flags={:?})",
                        test.tc_id,
                        test.result,
                        test.flags,
                    );
                }
            }
            tests_run += 1;
        }
    }

    assert!(tests_run > 0, "No tests were run");
    println!(
        "Ran {tests_run} X25519 tests ({} total)",
        test_set.number_of_tests
    );
}
