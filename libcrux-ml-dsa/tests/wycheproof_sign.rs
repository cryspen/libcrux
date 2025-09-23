// This module tests the implementation against the Wycheproof signing
// test vectors for the final version of the ML-DSA standard (see `libcrux-kats` crate).
//
// This set of test vectors does not cover the pre-hashed variants of
// ML-DSA.

use libcrux_kats::wycheproof::mldsa::{sign_noseed_schema::*, MlDsaSignTestsNoSeed, ParameterSet};
use libcrux_ml_dsa::{
    ml_dsa_44::{self, MLDSA44SigningKey},
    ml_dsa_65::{self, MLDSA65SigningKey},
    ml_dsa_87::{self, MLDSA87SigningKey},
    MLDSASigningKey, SigningError,
};

macro_rules! wycheproof_sign_noseed_test {
    ($name:ident, $test_name:expr, $signing_key_type:ty, $sign:expr) => {
        #[test]
        fn $name() {
            let katfile_serialized = MlDsaSignTestsNoSeed::load($test_name);

            let signing_randomness = [0u8; 32];

            for test_group in katfile_serialized.test_groups {
                let signing_key_bytes = test_group.private_key;
                if signing_key_bytes.len() != <$signing_key_type>::len() {
                    // If the signing key size in the KAT does not match the
                    // signing key size in our implementation, ensure that the KAT
                    // key has a corresponding flag set staring that its length is incorrect.
                    //
                    // This flag is set on the child `tests` object.
                    assert_eq!(test_group.tests.len(), 1);
                    assert!(test_group.tests[0]
                        .flags
                        .contains(&Flag::IncorrectPrivateKeyLength));

                    continue;
                }
                let signing_key = MLDSASigningKey::new(signing_key_bytes.try_into().unwrap());

                for test in test_group.tests {
                    let message = test.msg;
                    let context = test.ctx;

                    let signature = $sign(&signing_key, &message, &context, signing_randomness);

                    if let Err(SigningError::ContextTooLongError) = signature {
                        assert!(test.result == SignResult::Invalid)
                    }

                    if test.result == SignResult::Valid {
                        assert_eq!(signature.unwrap().as_slice(), test.sig.as_slice());
                    }
                    // TODO: else, the generated signature is invalid; we can
                    // check that our own implementation agrees with this judgement,
                    // but in order to do so we'd need the verification key.
                    // This is being tracked in https://github.com/cryspen/libcrux/issues/340
                }
            }
        }
    };
}

// 44

wycheproof_sign_noseed_test!(
    wycheproof_sign_44,
    ParameterSet::MlDsa44,
    MLDSA44SigningKey,
    ml_dsa_44::sign
);

wycheproof_sign_noseed_test!(
    wycheproof_sign_44_portable,
    ParameterSet::MlDsa44,
    MLDSA44SigningKey,
    ml_dsa_44::portable::sign
);

#[cfg(feature = "simd128")]
wycheproof_sign_noseed_test!(
    wycheproof_sign_44_simd128,
    ParameterSet::MlDsa44,
    MLDSA44SigningKey,
    ml_dsa_44::neon::sign
);

#[cfg(feature = "simd256")]
wycheproof_sign_noseed_test!(
    wycheproof_sign_44_simd256,
    ParameterSet::MlDsa44,
    MLDSA44SigningKey,
    ml_dsa_44::avx2::sign
);

// 65

wycheproof_sign_noseed_test!(
    wycheproof_sign_65,
    ParameterSet::MlDsa65,
    MLDSA65SigningKey,
    ml_dsa_65::sign
);

wycheproof_sign_noseed_test!(
    wycheproof_sign_65_portable,
    ParameterSet::MlDsa65,
    MLDSA65SigningKey,
    ml_dsa_65::portable::sign
);

#[cfg(feature = "simd128")]
wycheproof_sign_noseed_test!(
    wycheproof_sign_65_simd128,
    ParameterSet::MlDsa65,
    MLDSA65SigningKey,
    ml_dsa_65::neon::sign
);

#[cfg(feature = "simd256")]
wycheproof_sign_noseed_test!(
    wycheproof_sign_65_simd256,
    ParameterSet::MlDsa65,
    MLDSA65SigningKey,
    ml_dsa_65::avx2::sign
);

// 87

wycheproof_sign_noseed_test!(
    wycheproof_sign_87,
    ParameterSet::MlDsa87,
    MLDSA87SigningKey,
    ml_dsa_87::sign
);

wycheproof_sign_noseed_test!(
    wycheproof_sign_87_portable,
    ParameterSet::MlDsa87,
    MLDSA87SigningKey,
    ml_dsa_87::portable::sign
);

#[cfg(feature = "simd128")]
wycheproof_sign_noseed_test!(
    wycheproof_sign_87_simd128,
    ParameterSet::MlDsa87,
    MLDSA87SigningKey,
    ml_dsa_87::neon::sign
);

#[cfg(feature = "simd256")]
wycheproof_sign_noseed_test!(
    wycheproof_sign_87_simd256,
    ParameterSet::MlDsa87,
    MLDSA87SigningKey,
    ml_dsa_87::avx2::sign
);
