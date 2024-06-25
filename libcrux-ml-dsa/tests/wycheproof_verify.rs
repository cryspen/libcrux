use serde_json;

use hex;

use std::{fs::File, io::BufReader, path::Path};

use libcrux_ml_dsa::ml_dsa_44;

include!("wycheproof/verify_schema.rs");

#[test]
fn wycheproof_verify_44() {
    let katfile_path = Path::new("tests")
        .join("wycheproof")
        .join(format!("mldsa_{}_draft_verify_test.json", 44));
    let katfile = File::open(katfile_path).expect("Could not open KAT file.");
    let reader = BufReader::new(katfile);

    let katfile_serialized: VerifySchema =
        serde_json::from_reader(reader).expect("Could not deserialize KAT file.");

    for test_group in katfile_serialized.test_groups {
        let verification_key_bytes = hex::decode(test_group.public_key).unwrap();
        if verification_key_bytes.len() != ml_dsa_44::VERIFICATION_KEY_SIZE {
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
            ml_dsa_44::MLDSA44VerificationKey(verification_key_bytes.try_into().unwrap());

        for test in test_group.tests {
            let message = hex::decode(test.msg).unwrap();

            let signature_bytes = hex::decode(test.sig).unwrap();
            if signature_bytes.len() != ml_dsa_44::SIGNATURE_SIZE {
                // If the signature size in the KAT does not match the
                // signature size in our implementation, ensure that the KAT
                // signature has a corresponding flag set staring that its length
                // is incorrect.
                assert!(test.flags.contains(&Flag::IncorrectSignatureLength));

                continue;
            }
            let signature = ml_dsa_44::MLDSA44Signature(signature_bytes.try_into().unwrap());

            let verification_result = ml_dsa_44::verify(verification_key, &message, signature);

            match test.result {
                Result::Valid => assert!(verification_result.is_ok()),
                Result::Invalid => assert!(verification_result.is_err()),
            }
        }
    }
}
