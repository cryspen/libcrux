use libcrux_ml_kem::{mlkem1024, mlkem512, mlkem768};
use serde::Deserialize;
use serde_json;
use std::{fs::File, io::BufReader, path::Path};

use libcrux_sha3::*;

#[derive(Deserialize)]
struct KyberNISTKAT {
    #[serde(with = "hex::serde")]
    key_generation_seed: [u8; 64],

    #[serde(with = "hex::serde")]
    sha3_256_hash_of_public_key: [u8; 32],

    #[serde(with = "hex::serde")]
    sha3_256_hash_of_secret_key: [u8; 32],

    #[serde(with = "hex::serde")]
    encapsulation_seed: [u8; 32],

    #[serde(with = "hex::serde")]
    sha3_256_hash_of_ciphertext: [u8; 32],

    #[serde(with = "hex::serde")]
    shared_secret: [u8; 32],
}

macro_rules! impl_nist_known_answer_tests {
    ($name:ident, $parameter_set: literal, $key_gen_derand:expr, $encapsulate_derand:expr, $decapsulate_derand: expr) => {
        #[test]
        fn $name() {
            let katfile_path = Path::new("tests")
                .join("kats")
                .join(format!("nistkats_{}.json", $parameter_set));
            let katfile = File::open(katfile_path).expect("Could not open KAT file.");
            let reader = BufReader::new(katfile);

            let nist_kats: Vec<KyberNISTKAT> =
                serde_json::from_reader(reader).expect("Could not deserialize KAT file.");

            for kat in nist_kats {
                let key_pair = $key_gen_derand(kat.key_generation_seed);

                let public_key_hash = sha256(key_pair.pk());
                let secret_key_hash = sha256(key_pair.sk());

                assert_eq!(public_key_hash, kat.sha3_256_hash_of_public_key, "lhs: computed public key hash, rhs: hash from kat");
                assert_eq!(secret_key_hash, kat.sha3_256_hash_of_secret_key, "lhs: computed secret key hash, rhs: hash from kat");

                let (ciphertext, shared_secret) =
                    $encapsulate_derand(key_pair.public_key(), kat.encapsulation_seed);
                let ciphertext_hash = sha256(ciphertext.as_ref());

                assert_eq!(ciphertext_hash, kat.sha3_256_hash_of_ciphertext, "lhs: computed ciphertext hash, rhs: hash from akt");
                assert_eq!(shared_secret.as_ref(), kat.shared_secret, "lhs: computed shared secret from encapsulate, rhs: shared secret from kat");

                let shared_secret_from_decapsulate =
                    $decapsulate_derand(key_pair.private_key(), &ciphertext);
                assert_eq!(shared_secret_from_decapsulate, shared_secret.as_ref(), "lhs: shared secret computed via decapsulation, rhs: shared secret computed via encapsulation");
            }
        }
    };
}

impl_nist_known_answer_tests!(
    kyber512_nist_known_answer_tests,
    512,
    mlkem512::generate_key_pair,
    mlkem512::encapsulate,
    mlkem512::decapsulate
);
impl_nist_known_answer_tests!(
    kyber768_nist_known_answer_tests,
    768,
    mlkem768::generate_key_pair,
    mlkem768::encapsulate,
    mlkem768::decapsulate
);
impl_nist_known_answer_tests!(
    kyber1024_nist_known_answer_tests,
    1024,
    mlkem1024::generate_key_pair,
    mlkem1024::encapsulate,
    mlkem1024::decapsulate
);

// impl_nist_known_answer_tests!(
//     kyber768_nist_kats_portable,
//     768,
//     mlkem768::portable::generate_key_pair,
//     mlkem768::portable::encapsulate,
//     mlkem768::portable::decapsulate
// );
