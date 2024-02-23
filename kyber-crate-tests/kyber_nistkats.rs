use serde::Deserialize;
use serde_json;

use std::path::Path;
use std::{fs::File, io::BufReader};

use libcrux::digest;

use libcrux_kyber::kyber768::*;

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
                .join("kyber_kats")
                .join(format!("nistkats_{}.json", $parameter_set));
            let katfile = File::open(katfile_path).expect("Could not open KAT file.");
            let reader = BufReader::new(katfile);

            let nist_kats: Vec<KyberNISTKAT> =
                serde_json::from_reader(reader).expect("Could not deserialize KAT file.");

            for kat in nist_kats {
                eprintln!("seed: {}", hex::encode(kat.key_generation_seed));
                let key_pair = $key_gen_derand(kat.key_generation_seed);

                eprintln!("pk: {}", hex::encode(key_pair.pk()));
                eprintln!("sk: {}", hex::encode(key_pair.sk()));
                let public_key_hash = digest::sha3_256(key_pair.pk());
                let secret_key_hash = digest::sha3_256(key_pair.sk());

                // eprintln!("pk hash: {:x?}", public_key_hash);
                assert_eq!(public_key_hash, kat.sha3_256_hash_of_public_key, "public keys don't match");
                assert_eq!(secret_key_hash, kat.sha3_256_hash_of_secret_key, "secret keys don't match");

                let (ciphertext, shared_secret) =
                    $encapsulate_derand(key_pair.public_key(), kat.encapsulation_seed);
                let ciphertext_hash = digest::sha3_256(ciphertext.as_ref());

                assert_eq!(ciphertext_hash, kat.sha3_256_hash_of_ciphertext, "ciphertexts don't match");
                assert_eq!(shared_secret.as_ref(), kat.shared_secret, "shared secret produced by encapsulate does not match");

                let shared_secret_from_decapsulate =
                    $decapsulate_derand(key_pair.private_key(), &ciphertext);
                assert_eq!(shared_secret_from_decapsulate, shared_secret.as_ref(), "shared secret produced by decapsulate doesn't match the one produced by encapsulate");
                break;
            }
        }
    };
}

impl_nist_known_answer_tests!(
    kyber768_nist_known_answer_tests,
    768,
    generate_key_pair,
    encapsulate,
    decapsulate
);
