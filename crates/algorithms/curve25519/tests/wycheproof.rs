use wycheproof::{xdh, TestResult};

#[test]
fn x25519() {
    let test_set = xdh::TestSet::load(xdh::TestName::X25519).unwrap();
    let mut tests_run = 0;

    for test_group in test_set.test_groups {
        for test in &test_group.tests {
            if test.public_key.len() != 32 || test.private_key.len() != 32 {
                assert_eq!(test.result, TestResult::Invalid);
                tests_run += 1;
                continue;
            }

            let pk: [u8; 32] = test.public_key[..].try_into().unwrap();
            let sk: [u8; 32] = test.private_key[..].try_into().unwrap();
            let mut out = [0u8; 32];

            // HACL rejects some "acceptable" vectors that produce low-order
            // or twist points resulting in a zero shared secret.
            let hacl_rejects = test.flags.iter().any(|f| {
                matches!(
                    f,
                    xdh::TestFlag::LowOrderPublic
                        | xdh::TestFlag::SmallPublicKey
                        | xdh::TestFlag::ZeroSharedSecret
                )
            });

            match libcrux_curve25519::ecdh(&mut out, &pk, &sk) {
                Ok(()) => {
                    assert_eq!(
                        &out[..],
                        test.shared_secret.as_ref(),
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
    println!("Ran {tests_run} X25519 tests ({} total)", test_set.number_of_tests);
}
