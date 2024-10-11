// This module tests the implementation against the Wycheproof verification
// test vectors for the final version of the ML-DSA standard, added in
// commit
// [https://github.com/C2SP/wycheproof/pull/112/commits/8e7fa6f87e6993d7b613cf48b46512a32df8084a].
//
// This set of test vectors does not cover the pre-hashed variants of
// ML-DSA.

use serde_json;

use hex;

use std::{fs::File, io::BufReader, path::Path};

use libcrux_ml_dsa::{ml_dsa_44, ml_dsa_65, ml_dsa_87, MLDSASignature, MLDSAVerificationKey};

include!("wycheproof/verify_schema.rs");

macro_rules! wycheproof_verify_test {
    ($name:ident, $parameter_set:literal, $verification_key_object:ty, $signature_object:ty, $verify:expr) => {
        #[test]
        fn $name() {
            let katfile_path = Path::new("tests").join("wycheproof").join(format!(
                "mldsa_{}_standard_verify_test.json",
                $parameter_set
            ));
            let katfile = File::open(katfile_path).expect("Could not open KAT file.");
            let reader = BufReader::new(katfile);

            let katfile_serialized: VerifySchema =
                serde_json::from_reader(reader).expect("Could not deserialize KAT file.");

            for test_group in katfile_serialized.test_groups {
                let verification_key_bytes = hex::decode(test_group.public_key).unwrap();
                if verification_key_bytes.len() != <$verification_key_object>::len() {
                    // If the verification key size in the KAT does not match the
                    // verification key size in our implementation, ensure that the KAT
                    // key has a corresponding flag set staring that its length is incorrect.
                    //
                    // This flag is set on the child `tests` object.
                    assert_eq!(test_group.tests.len(), 1);
                    assert!(test_group.tests[0]
                        .flags
                        .contains(&Flag::IncorrectPublicKeyLength));

                    continue;
                }
                let verification_key =
                    MLDSAVerificationKey(verification_key_bytes.try_into().unwrap());

                for test in test_group.tests {
                    let message = hex::decode(test.msg).unwrap();
                    let context = hex::decode(test.ctx).unwrap();
                    let signature_bytes = hex::decode(test.sig).unwrap();
                    if signature_bytes.len() != <$signature_object>::len() {
                        // If the signature size in the KAT does not match the
                        // signature size in our implementation, ensure that the KAT
                        // signature has a corresponding flag set staring that its length
                        // is incorrect.
                        assert!(test.flags.contains(&Flag::IncorrectSignatureLength));

                        continue;
                    }
                    let signature = MLDSASignature(signature_bytes.try_into().unwrap());

                    let verification_result =
                        $verify(&verification_key, &message, &context, &signature);

                    match test.result {
                        Result::Valid => assert!(verification_result.is_ok()),
                        Result::Invalid => assert!(verification_result.is_err()),
                    }
                }
            }
        }
    };
}

// 44

wycheproof_verify_test!(
    wycheproof_verify_44,
    44,
    ml_dsa_44::MLDSA44VerificationKey,
    ml_dsa_44::MLDSA44Signature,
    ml_dsa_44::verify
);

wycheproof_verify_test!(
    wycheproof_verify_44_portable,
    44,
    ml_dsa_44::MLDSA44VerificationKey,
    ml_dsa_44::MLDSA44Signature,
    ml_dsa_44::portable::verify
);

#[cfg(feature = "simd128")]
wycheproof_verify_test!(
    wycheproof_verify_44_simd128,
    44,
    ml_dsa_44::MLDSA44VerificationKey,
    ml_dsa_44::MLDSA44Signature,
    ml_dsa_44::neon::verify
);

#[cfg(feature = "simd256")]
wycheproof_verify_test!(
    wycheproof_verify_44_simd256,
    44,
    ml_dsa_44::MLDSA44VerificationKey,
    ml_dsa_44::MLDSA44Signature,
    ml_dsa_44::avx2::verify
);

// 65

wycheproof_verify_test!(
    wycheproof_verify_65,
    65,
    ml_dsa_65::MLDSA65VerificationKey,
    ml_dsa_65::MLDSA65Signature,
    ml_dsa_65::verify
);

wycheproof_verify_test!(
    wycheproof_verify_65_portable,
    65,
    ml_dsa_65::MLDSA65VerificationKey,
    ml_dsa_65::MLDSA65Signature,
    ml_dsa_65::portable::verify
);

#[cfg(feature = "simd128")]
wycheproof_verify_test!(
    wycheproof_verify_65_simd128,
    65,
    ml_dsa_65::MLDSA65VerificationKey,
    ml_dsa_65::MLDSA65Signature,
    ml_dsa_65::neon::verify
);

#[cfg(feature = "simd256")]
wycheproof_verify_test!(
    wycheproof_verify_65_simd256,
    65,
    ml_dsa_65::MLDSA65VerificationKey,
    ml_dsa_65::MLDSA65Signature,
    ml_dsa_65::avx2::verify
);

// 87

wycheproof_verify_test!(
    wycheproof_verify_87,
    87,
    ml_dsa_87::MLDSA87VerificationKey,
    ml_dsa_87::MLDSA87Signature,
    ml_dsa_87::verify
);

wycheproof_verify_test!(
    wycheproof_verify_87_portable,
    87,
    ml_dsa_87::MLDSA87VerificationKey,
    ml_dsa_87::MLDSA87Signature,
    ml_dsa_87::portable::verify
);

#[cfg(feature = "simd128")]
wycheproof_verify_test!(
    wycheproof_verify_87_simd128,
    87,
    ml_dsa_87::MLDSA87VerificationKey,
    ml_dsa_87::MLDSA87Signature,
    ml_dsa_87::neon::verify
);

#[cfg(feature = "simd256")]
wycheproof_verify_test!(
    wycheproof_verify_87_simd256,
    87,
    ml_dsa_87::MLDSA87VerificationKey,
    ml_dsa_87::MLDSA87Signature,
    ml_dsa_87::avx2::verify
);
