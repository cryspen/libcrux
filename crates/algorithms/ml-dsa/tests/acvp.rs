#![cfg(feature = "acvp")]

use libcrux_kats::acvp::mldsa::keygen_schema::*;
use libcrux_kats::acvp::mldsa::sign_schema::*;
use libcrux_kats::acvp::mldsa::verify_schema::*;
use libcrux_kats::acvp::schema_common::*;

#[test]
fn keygen() {
    use libcrux_kats::acvp::mldsa::KeyGenTests;

    let KeyGenTests { prompts, results } = KeyGenTests::load();
    // checks
    assert!(prompts.algorithm == "ML-DSA");
    assert!(prompts.revision == "FIPS204");
    assert!(results.algorithm == "ML-DSA");
    assert!(results.revision == "FIPS204");

    for kat in prompts.testGroups {
        let parameter_set = kat.parameterSet;
        assert!(
            parameter_set == "ML-DSA-44"
                || parameter_set == "ML-DSA-65"
                || parameter_set == "ML-DSA-87"
        );
        eprintln!("{parameter_set}");

        for test in kat.tests {
            keygen_inner(test, &results, kat.tgId, &parameter_set);
        }
    }
}

#[inline(never)]
#[allow(non_snake_case)]
fn keygen_inner(
    test: KeyGenPrompt,
    results: &Results<ResultKeyGenTestGroup>,
    tgId: usize,
    parameter_set: &String,
) {
    use libcrux_ml_dsa::*;
    eprintln!("  {}", test.tcId);
    #[inline(never)]
    fn check<const VK_LEN: usize, const SK_LEN: usize>(
        keys: MLDSAKeyPair<VK_LEN, SK_LEN>,
        result: &KeyGenResult,
    ) {
        assert_eq!(result.pk, keys.verification_key.as_slice());
        assert_eq!(result.sk, keys.signing_key.as_slice());
    }

    let expected_result = results.find_expected_result(tgId, test.tcId);

    match parameter_set.as_str() {
        "ML-DSA-44" => check(ml_dsa_44::generate_key_pair(test.seed), expected_result),

        "ML-DSA-65" => check(ml_dsa_65::generate_key_pair(test.seed), expected_result),

        "ML-DSA-87" => check(ml_dsa_87::generate_key_pair(test.seed), expected_result),
        _ => unimplemented!(),
    }
}

#[test]
fn siggen() {
    use libcrux_kats::acvp::mldsa::SigGenTests;

    let SigGenTests { prompts, results } = SigGenTests::load();
    // checks
    assert!(prompts.algorithm == "ML-DSA");
    assert!(prompts.revision == "FIPS204");
    assert!(results.algorithm == "ML-DSA");
    assert!(results.revision == "FIPS204");

    for kat in prompts.testGroups {
        let parameter_set = kat.parameterSet;
        assert!(
            parameter_set == "ML-DSA-44"
                || parameter_set == "ML-DSA-65"
                || parameter_set == "ML-DSA-87"
        );
        eprintln!("{parameter_set}");

        for test in kat.tests {
            if kat.signatureInterface == "internal" {
                if kat.externalMu {
                    // NOTE: this API is currently not supported
                    eprintln!(
                        "Skipping test tgId {tgId}, tcId {tcId}: externalMu = true",
                        tgId = kat.tgId,
                        tcId = test.tcId,
                    );
                    continue;
                }
                siggen_inner_internal(test, &results, kat.tgId, &parameter_set)
            } else {
                let pre_hash = kat.preHash == Some("preHash".to_string());
                if pre_hash {
                    if test.hashAlg.as_ref().map(String::as_str) != Some("SHAKE-128") {
                        eprintln!("Skipping pre-hash {:?}: unsupported", test.hashAlg);
                        continue;
                    }
                    siggen_inner_external_prehash(test, &results, kat.tgId, &parameter_set);
                } else {
                    siggen_inner_external(test, &results, kat.tgId, &parameter_set);
                }
            }
        }
    }
}

#[inline(never)]
#[allow(non_snake_case)]
fn siggen_inner_internal(
    test: SigGenTest,
    results: &Results<ResultSigGenTestGroup>,
    tgId: usize,
    parameter_set: &String,
) {
    use libcrux_ml_dsa::*;
    eprintln!("  {}", test.tcId);

    let Randomness(rnd) = test.rnd.unwrap_or(Randomness([0u8; 32]));

    let expected_result = results.find_expected_result(tgId, test.tcId);

    match parameter_set.as_str() {
        "ML-DSA-44" => {
            let signature = ml_dsa_44::sign_internal(
                &MLDSASigningKey::new(test.sk.try_into().unwrap()),
                &test.message,
                rnd,
            )
            .unwrap();
            assert_eq!(signature.as_slice(), expected_result.signature);
        }

        "ML-DSA-65" => {
            let signature = ml_dsa_65::sign_internal(
                &MLDSASigningKey::new(test.sk.try_into().unwrap()),
                &test.message,
                rnd,
            )
            .unwrap();
            assert_eq!(signature.as_slice(), expected_result.signature);
        }

        "ML-DSA-87" => {
            let signature = ml_dsa_87::sign_internal(
                &MLDSASigningKey::new(test.sk.try_into().unwrap()),
                &test.message,
                rnd,
            )
            .unwrap();
            assert_eq!(signature.as_slice(), expected_result.signature);
        }
        _ => unimplemented!(),
    }
}

macro_rules! siggen_test {
    ($name:ident, $sign:ident) => {
        #[inline(never)]
        #[allow(non_snake_case)]
        fn $name(
            test: SigGenTest,
            results: &Results<ResultSigGenTestGroup>,
            tgId: usize,
            parameter_set: &String,
        ) {
            use libcrux_ml_dsa::*;

            eprintln!("  {}", test.tcId);

            let Randomness(rnd) = test.rnd.unwrap_or(Randomness([0u8; 32]));

            let expected_result = results.find_expected_result(tgId, test.tcId);

            match parameter_set.as_str() {
                "ML-DSA-44" => {
                    let signature = ml_dsa_44::$sign(
                        &MLDSASigningKey::new(test.sk.try_into().unwrap()),
                        &test.message,
                        &test.context,
                        rnd,
                    )
                    .unwrap();
                    assert_eq!(signature.as_slice(), expected_result.signature);
                }

                "ML-DSA-65" => {
                    let signature = ml_dsa_65::$sign(
                        &MLDSASigningKey::new(test.sk.try_into().unwrap()),
                        &test.message,
                        &test.context,
                        rnd,
                    )
                    .unwrap();
                    assert_eq!(signature.as_slice(), expected_result.signature);
                }

                "ML-DSA-87" => {
                    let signature = ml_dsa_87::$sign(
                        &MLDSASigningKey::new(test.sk.try_into().unwrap()),
                        &test.message,
                        &test.context,
                        rnd,
                    )
                    .unwrap();
                    assert_eq!(signature.as_slice(), expected_result.signature);
                }
                _ => unimplemented!(),
            }
        }
    };
}
siggen_test!(siggen_inner_external, sign);
siggen_test!(siggen_inner_external_prehash, sign_pre_hashed_shake128);

#[test]
fn sigver() {
    use libcrux_kats::acvp::mldsa::SigVerTests;

    let SigVerTests { prompts, results } = SigVerTests::load();
    // checks
    assert!(prompts.algorithm == "ML-DSA");
    assert!(prompts.revision == "FIPS204");
    assert!(results.algorithm == "ML-DSA");
    assert!(results.revision == "FIPS204");

    for kat in prompts.testGroups {
        let parameter_set = kat.parameterSet;
        assert!(
            parameter_set == "ML-DSA-44"
                || parameter_set == "ML-DSA-65"
                || parameter_set == "ML-DSA-87"
        );
        eprintln!("{parameter_set}");

        for test in kat.tests {
            if kat.signatureInterface == "internal" {
                if kat.externalMu {
                    // NOTE: this API is currently not supported
                    eprintln!(
                        "Skipping test tgId {tgId}, tcId {tcId}: externalMu = true",
                        tgId = kat.tgId,
                        tcId = test.tcId,
                    );
                    continue;
                }
                sigver_inner_internal(test, &results, kat.tgId, &parameter_set);
            } else {
                let pre_hash = kat.preHash == Some("preHash".to_string());
                if pre_hash && test.hashAlg.as_ref().map(String::as_str) != Some("SHAKE-128") {
                    eprintln!("Skipping pre-hash {:?}: unsupported", test.hashAlg);
                    continue;
                }
                sigver_inner_external(test, &results, kat.tgId, &parameter_set, pre_hash);
            }
        }
    }
}
#[inline(never)]
#[allow(non_snake_case)]
fn sigver_inner_external(
    test: SigVerTest,
    results: &Results<ResultSigVerTestGroup>,
    tgId: usize,
    parameter_set: &String,
    pre_hash: bool,
) {
    use libcrux_ml_dsa::*;
    eprintln!("  {}", test.tcId);
    let expected_result = results.find_expected_result(tgId, test.tcId);

    let pk = test.pk.to_owned();

    match parameter_set.as_str() {
        "ML-DSA-44" => {
            let verify = match pre_hash {
                false => ml_dsa_44::verify,
                true => ml_dsa_44::verify_pre_hashed_shake128,
            };
            let valid = verify(
                &MLDSAVerificationKey::new(pk.try_into().unwrap()),
                &test.message,
                &test.context,
                &MLDSASignature::new(test.signature.try_into().unwrap()),
            );
            assert_eq!(valid.is_ok(), expected_result.testPassed);
        }

        "ML-DSA-65" => {
            let verify = match pre_hash {
                false => ml_dsa_65::verify,
                true => ml_dsa_65::verify_pre_hashed_shake128,
            };
            let valid = verify(
                &MLDSAVerificationKey::new(pk.try_into().unwrap()),
                &test.message,
                &test.context,
                &MLDSASignature::new(test.signature.try_into().unwrap()),
            );
            assert_eq!(valid.is_ok(), expected_result.testPassed);
        }

        "ML-DSA-87" => {
            let verify = match pre_hash {
                false => ml_dsa_87::verify,
                true => ml_dsa_87::verify_pre_hashed_shake128,
            };
            let valid = verify(
                &MLDSAVerificationKey::new(pk.try_into().unwrap()),
                &test.message,
                &test.context,
                &MLDSASignature::new(test.signature.try_into().unwrap()),
            );
            assert_eq!(valid.is_ok(), expected_result.testPassed);
        }
        _ => unimplemented!(),
    }
}

#[inline(never)]
#[allow(non_snake_case)]
fn sigver_inner_internal(
    test: SigVerTest,
    results: &Results<ResultSigVerTestGroup>,
    tgId: usize,
    parameter_set: &String,
) {
    use libcrux_ml_dsa::*;
    eprintln!("  {}", test.tcId);
    let expected_result = results.find_expected_result(tgId, test.tcId);

    let pk = test.pk.to_owned();

    match parameter_set.as_str() {
        "ML-DSA-44" => {
            let valid = ml_dsa_44::verify_internal(
                &MLDSAVerificationKey::new(pk.try_into().unwrap()),
                &test.message,
                &MLDSASignature::new(test.signature.try_into().unwrap()),
            );
            assert_eq!(valid.is_ok(), expected_result.testPassed);
        }

        "ML-DSA-65" => {
            let valid = ml_dsa_65::verify_internal(
                &MLDSAVerificationKey::new(pk.try_into().unwrap()),
                &test.message,
                &MLDSASignature::new(test.signature.try_into().unwrap()),
            );
            assert_eq!(valid.is_ok(), expected_result.testPassed);
        }

        "ML-DSA-87" => {
            let valid = ml_dsa_87::verify_internal(
                &MLDSAVerificationKey::new(pk.try_into().unwrap()),
                &test.message,
                &MLDSASignature::new(test.signature.try_into().unwrap()),
            );
            assert_eq!(valid.is_ok(), expected_result.testPassed);
        }
        _ => unimplemented!(),
    }
}
