use serde_json;

use hex;

use std::{fs::File, io::BufReader, path::Path};

use libcrux_ml_dsa::{ml_dsa_44, ml_dsa_65, ml_dsa_87};

include!("wycheproof/sign_schema.rs");

macro_rules! wycheproof_sign_test {
    ($name:ident, $parameter_set:literal, $signing_key_size:expr, $signing_key_object: expr, $sign:expr) => {
        #[test]
        fn $name() {
            let katfile_path = Path::new("tests")
                .join("wycheproof")
                .join(format!("mldsa_{}_draft_sign_test.json", $parameter_set));
            let katfile = File::open(katfile_path).expect("Could not open KAT file.");
            let reader = BufReader::new(katfile);

            let katfile_serialized: SignSchema =
                serde_json::from_reader(reader).expect("Could not deserialize KAT file.");

            let signing_randomness = [0u8; 32];

            for test_group in katfile_serialized.test_groups {
                let signing_key_bytes = hex::decode(test_group.private_key).unwrap();
                if signing_key_bytes.len() != $signing_key_size {
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
                let signing_key = $signing_key_object(signing_key_bytes.try_into().unwrap());

                for test in test_group.tests {
                    let message = hex::decode(test.msg).unwrap();

                    let signature = $sign(signing_key, &message, signing_randomness);

                    if test.result == Result::Valid {
                        assert_eq!(
                            signature.0.as_slice(),
                            hex::decode(test.sig).unwrap().as_slice()
                        );
                    } // TODO: else, how should invalid signatures be handled?
                }
            }
        }
    };
}

wycheproof_sign_test!(
    wycheproof_sign_44,
    44,
    ml_dsa_44::SIGNING_KEY_SIZE,
    ml_dsa_44::MLDSA44SigningKey,
    ml_dsa_44::sign
);
wycheproof_sign_test!(
    wycheproof_sign_65,
    65,
    ml_dsa_65::SIGNING_KEY_SIZE,
    ml_dsa_65::MLDSA65SigningKey,
    ml_dsa_65::sign
);
wycheproof_sign_test!(
    wycheproof_sign_87,
    87,
    ml_dsa_87::SIGNING_KEY_SIZE,
    ml_dsa_87::MLDSA87SigningKey,
    ml_dsa_87::sign
);
