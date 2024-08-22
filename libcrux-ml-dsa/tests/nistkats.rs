use serde::Deserialize;
use serde_json;

use hex;

use std::{fs::File, io::BufReader, path::Path};

#[derive(Debug, Deserialize)]
struct MlDsaNISTKAT {
    #[serde(with = "hex::serde")]
    key_generation_seed: [u8; 32],

    #[serde(with = "hex::serde")]
    sha3_256_hash_of_verification_key: [u8; 32],

    #[serde(with = "hex::serde")]
    sha3_256_hash_of_signing_key: [u8; 32],

    // The length of the message in each KAT is 33 * (i + 1), where i is the
    // 0-indexed KAT counter.
    message: String,

    #[serde(with = "hex::serde")]
    signing_randomness: [u8; 32],

    #[serde(with = "hex::serde")]
    sha3_256_hash_of_signature: [u8; 32],
}

macro_rules! impl_nist_known_answer_tests {
    ($name:ident, $parameter_set:literal, $key_gen:expr, $sign:expr, $verify:expr) => {
        #[test]
        fn $name() {
            let katfile_path = Path::new("tests")
                .join("kats")
                .join(format!("nistkats-{}.json", $parameter_set));
            let katfile = File::open(katfile_path).expect("Could not open KAT file.");
            let reader = BufReader::new(katfile);

            let nist_kats: Vec<MlDsaNISTKAT> =
                serde_json::from_reader(reader).expect("Could not deserialize KAT file.");

            for kat in nist_kats {
                let key_pair = $key_gen(kat.key_generation_seed);

                let verification_key_hash = libcrux_sha3::sha256(&key_pair.verification_key.0);
                assert_eq!(
                    verification_key_hash, kat.sha3_256_hash_of_verification_key,
                    "verification_key_hash != kat.sha3_256_hash_of_verification_key"
                );

                let signing_key_hash = libcrux_sha3::sha256(&key_pair.signing_key.0);
                assert_eq!(
                    signing_key_hash, kat.sha3_256_hash_of_signing_key,
                    "signing_key_hash != kat.sha3_256_hash_of_signing_key"
                );

                let message = hex::decode(kat.message).expect("Hex-decoding the message failed.");

                let signature = $sign(&key_pair.signing_key, &message, kat.signing_randomness);

                let signature_hash = libcrux_sha3::sha256(&signature.0);
                assert_eq!(
                    signature_hash, kat.sha3_256_hash_of_signature,
                    "signature_hash != kat.sha3_256_hash_of_signature"
                );

                $verify(&key_pair.verification_key, &message, &signature)
                    .expect("Verification should pass since the signature was honestly generated");
            }
        }
    };
}

impl_nist_known_answer_tests!(
    nist_known_answer_tests_44,
    44,
    libcrux_ml_dsa::ml_dsa_44::generate_key_pair,
    libcrux_ml_dsa::ml_dsa_44::sign,
    libcrux_ml_dsa::ml_dsa_44::verify
);

impl_nist_known_answer_tests!(
    nist_known_answer_tests_65,
    65,
    libcrux_ml_dsa::ml_dsa_65::generate_key_pair,
    libcrux_ml_dsa::ml_dsa_65::sign,
    libcrux_ml_dsa::ml_dsa_65::verify
);

impl_nist_known_answer_tests!(
    nist_known_answer_tests_87,
    87,
    libcrux_ml_dsa::ml_dsa_87::generate_key_pair,
    libcrux_ml_dsa::ml_dsa_87::sign,
    libcrux_ml_dsa::ml_dsa_87::verify
);
