use libcrux::kem;
use serde::Deserialize;
use serde_json;

use libcrux::digest;

use std::{fs::File, io::BufReader};

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

fn nist_known_answer_tests(path_to_kat_file: &str) {
    let katfile = File::open(path_to_kat_file).expect("Could not open KAT file.");
    let reader = BufReader::new(katfile);

    let nist_kats: Vec<KyberNISTKAT> =
        serde_json::from_reader(reader).expect("Could not deserialize KAT file.");

    for kat in nist_kats {
        let key_pair = kem::kyber768_generate_keypair_derand(kat.key_generation_seed).unwrap();

        let public_key_hash = digest::sha3_256(key_pair.pk());
        for i in 0..public_key_hash.len() {
            assert_eq!(public_key_hash[i], kat.sha3_256_hash_of_public_key[i]);
        }

        let secret_key_hash = digest::sha3_256(key_pair.sk());
        for i in 0..secret_key_hash.len() {
            assert_eq!(secret_key_hash[i], kat.sha3_256_hash_of_secret_key[i]);
        }

        let (ciphertext, shared_secret) =
            kem::kyber768_encapsulate_derand(key_pair.public_key(), kat.encapsulation_seed)
                .unwrap();

        let ciphertext_hash = digest::sha3_256(ciphertext.as_ref());
        for i in 0..ciphertext_hash.len() {
            assert_eq!(ciphertext_hash[i], kat.sha3_256_hash_of_ciphertext[i]);
        }

        for i in 0..shared_secret.len() {
            assert_eq!(shared_secret[i], kat.shared_secret[i]);
        }

        let shared_secret_from_decapsulate =
            kem::kyber768_decapsulate_derand(key_pair.private_key(), &ciphertext);
        for i in 0..shared_secret.len() {
            assert_eq!(shared_secret_from_decapsulate[i], shared_secret[i]);
        }
    }
}

#[test]
fn kyber768_nist_known_answer_tests() {
    nist_known_answer_tests("tests/kyber_kats/nistkats_768.json");
}
