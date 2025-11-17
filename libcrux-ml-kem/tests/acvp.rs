#![cfg(any(feature = "mlkem512", feature = "mlkem768", feature = "mlkem1024",))]

use libcrux_kats::acvp::mlkem::{encap_decap_schema::*, keygen_schema::*, *};

#[test]
fn keygen() {
    use libcrux_ml_kem::*;

    let KeyGenTests { prompts, results } = KeyGenTests::load();
    assert!(prompts.algorithm == "ML-KEM");
    assert!(prompts.revision == "FIPS203");

    assert!(results.algorithm == "ML-KEM");
    assert!(results.revision == "FIPS203");

    for kat in prompts.testGroups {
        let parameter_set = kat.parameterSet;
        assert!(
            parameter_set == "ML-KEM-512"
                || parameter_set == "ML-KEM-768"
                || parameter_set == "ML-KEM-1024"
        );
        eprintln!("{parameter_set}");

        for test in kat.tests {
            eprintln!("  {}", test.tcId);
            let mut seed = [0u8; 64];
            seed[..32].copy_from_slice(&test.d);
            seed[32..].copy_from_slice(&test.z);

            fn check<const EK_LEN: usize, const DK_LEN: usize>(
                keys: MlKemKeyPair<DK_LEN, EK_LEN>,
                result: &KeyGenResult,
            ) {
                assert_eq!(result.ek, keys.pk());
                assert_eq!(result.dk, keys.sk());
            }

            let expected_result = results.find_expected_result(kat.tgId, test.tcId);

            match parameter_set.as_str() {
                "ML-KEM-512" =>
                {
                    #[cfg(feature = "mlkem512")]
                    check(mlkem512::generate_key_pair(seed), expected_result)
                }

                "ML-KEM-768" =>
                {
                    #[cfg(feature = "mlkem768")]
                    check(mlkem768::generate_key_pair(seed), expected_result)
                }

                "ML-KEM-1024" =>
                {
                    #[cfg(feature = "mlkem1024")]
                    check(mlkem1024::generate_key_pair(seed), expected_result)
                }
                _ => unimplemented!(),
            }
        }
    }
}

#[test]
fn encap_decap() {
    use libcrux_ml_kem::*;

    let EncapDecapTests { prompts, results } = EncapDecapTests::load();
    assert!(prompts.algorithm == "ML-KEM");
    assert!(prompts.revision == "FIPS203");

    assert!(results.algorithm == "ML-KEM");
    assert!(results.revision == "FIPS203");

    for kat in prompts.testGroups {
        let parameter_set = kat.parameterSet;
        assert!(
            parameter_set == "ML-KEM-512"
                || parameter_set == "ML-KEM-768"
                || parameter_set == "ML-KEM-1024"
        );
        eprintln!("{parameter_set}");

        match kat.tests {
            EncapDecapTestPrompts::EncapTests { tests } => {
                for test in tests {
                    let expected_result = results.find_expected_result(kat.tgId, test.tcId);

                    let EncapDecapResult::EncapResult { c, k, .. } = expected_result else {
                        unreachable!()
                    };

                    let ek = test.ek;
                    let randomness = test.m;
                    match parameter_set.as_str() {
                        "ML-KEM-512" => {
                            #[cfg(feature = "mlkem512")]
                            {
                                let (actual_ct, actual_k) = mlkem512::encapsulate(
                                    &mlkem512::MlKem512PublicKey::try_from(ek.as_slice()).unwrap(),
                                    randomness,
                                );
                                assert_eq!(actual_ct.as_ref(), c);
                                assert_eq!(actual_k.as_ref(), k);
                            }
                        }
                        "ML-KEM-768" => {
                            #[cfg(feature = "mlkem768")]
                            {
                                let (actual_ct, actual_k) = mlkem768::encapsulate(
                                    &mlkem768::MlKem768PublicKey::try_from(ek.as_slice()).unwrap(),
                                    randomness,
                                );
                                assert_eq!(actual_ct.as_ref(), c);
                                assert_eq!(actual_k.as_ref(), k);
                            }
                        }
                        "ML-KEM-1024" => {
                            #[cfg(feature = "mlkem1024")]
                            {
                                let (actual_ct, actual_k) = mlkem1024::encapsulate(
                                    &mlkem1024::MlKem1024PublicKey::try_from(ek.as_slice())
                                        .unwrap(),
                                    randomness,
                                );
                                assert_eq!(actual_ct.as_ref(), c);
                                assert_eq!(actual_k.as_ref(), k);
                            }
                        }
                        _ => unimplemented!(),
                    }
                }
            }
            EncapDecapTestPrompts::DecapTests { tests } => {
                for test in tests {
                    let expected_result = results.find_expected_result(kat.tgId, test.tcId);

                    let EncapDecapResult::DecapResult { k, .. } = expected_result else {
                        unreachable!()
                    };

                    let c = test.c;
                    match parameter_set.as_str() {
                        "ML-KEM-512" => {
                            #[cfg(feature = "mlkem512")]
                            {
                                let dk = mlkem512::MlKem512PrivateKey::try_from(test.dk.as_slice())
                                    .unwrap();
                                let c =
                                    mlkem512::MlKem512Ciphertext::try_from(c.as_slice()).unwrap();
                                let actual_k = mlkem512::decapsulate(&dk, &c);
                                assert_eq!(actual_k.as_ref(), k);
                            }
                        }
                        "ML-KEM-768" => {
                            #[cfg(feature = "mlkem768")]
                            {
                                let dk = mlkem768::MlKem768PrivateKey::try_from(test.dk.as_slice())
                                    .unwrap();
                                let c =
                                    mlkem768::MlKem768Ciphertext::try_from(c.as_slice()).unwrap();
                                let actual_k = mlkem768::decapsulate(&dk, &c);
                                assert_eq!(actual_k.as_ref(), k);
                            }
                        }
                        "ML-KEM-1024" => {
                            #[cfg(feature = "mlkem1024")]
                            {
                                let dk =
                                    mlkem1024::MlKem1024PrivateKey::try_from(test.dk.as_slice())
                                        .unwrap();
                                let c =
                                    mlkem1024::MlKem1024Ciphertext::try_from(c.as_slice()).unwrap();
                                let actual_k = mlkem1024::decapsulate(&dk, &c);
                                assert_eq!(actual_k.as_ref(), k);
                            }
                        }

                        _ => unimplemented!(),
                    }
                }
            }
            EncapDecapTestPrompts::EncapKeyCheck { tests } => {
                for test in tests {
                    // check key
                    let succeeded = match parameter_set.as_str() {
                        "ML-KEM-512" => {
                            #[cfg(feature = "mlkem512")]
                            {
                                mlkem512::MlKem512PublicKey::try_from(test.ek.as_slice())
                                    .map(|ek| mlkem512::validate_public_key(&ek))
                                    .unwrap_or(false)
                            }
                        }
                        "ML-KEM-768" => {
                            #[cfg(feature = "mlkem768")]
                            {
                                mlkem768::MlKem768PublicKey::try_from(test.ek.as_slice())
                                    .map(|ek| mlkem768::validate_public_key(&ek))
                                    .unwrap_or(false)
                            }
                        }
                        "ML-KEM-1024" => {
                            #[cfg(feature = "mlkem1024")]
                            {
                                mlkem1024::MlKem1024PublicKey::try_from(test.ek.as_slice())
                                    .map(|ek| mlkem1024::validate_public_key(&ek))
                                    .unwrap_or(false)
                            }
                        }
                        _ => unimplemented!(),
                    };

                    // get result
                    let EncapDecapResult::KeyCheckResult { testPassed, .. } =
                        results.find_expected_result(kat.tgId, test.tcId)
                    else {
                        unreachable!();
                    };

                    assert_eq!(
                        succeeded, *testPassed,
                        "tgId: {}, tcId: {}",
                        kat.tgId, test.tcId
                    );
                }
            }
            EncapDecapTestPrompts::DecapKeyCheck { tests } => {
                for test in tests {
                    // check key
                    let succeeded = match parameter_set.as_str() {
                        "ML-KEM-512" => {
                            #[cfg(feature = "mlkem512")]
                            {
                                mlkem512::MlKem512PrivateKey::try_from(test.dk.as_slice())
                                    .map(|dk| mlkem512::portable::validate_private_key_only(&dk))
                                    .unwrap_or(false)
                            }
                        }
                        "ML-KEM-768" => {
                            #[cfg(feature = "mlkem768")]
                            {
                                mlkem768::MlKem768PrivateKey::try_from(test.dk.as_slice())
                                    .map(|dk| mlkem768::portable::validate_private_key_only(&dk))
                                    .unwrap_or(false)
                            }
                        }
                        "ML-KEM-1024" => {
                            #[cfg(feature = "mlkem1024")]
                            {
                                mlkem1024::MlKem1024PrivateKey::try_from(test.dk.as_slice())
                                    .map(|dk| mlkem1024::portable::validate_private_key_only(&dk))
                                    .unwrap_or(false)
                            }
                        }
                        _ => unimplemented!(),
                    };

                    // get result
                    let EncapDecapResult::KeyCheckResult { testPassed, .. } =
                        results.find_expected_result(kat.tgId, test.tcId)
                    else {
                        unreachable!();
                    };

                    assert_eq!(
                        succeeded, *testPassed,
                        "tgId: {}, tcId: {}",
                        kat.tgId, test.tcId
                    );
                }
            }
        }
    }
}
