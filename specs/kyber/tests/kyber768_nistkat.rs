extern crate hacspec_kyber;

use serde::Deserialize;
use serde_json;

use libcrux::digest;

use std::{fs::File, io::BufReader};

#[derive(Deserialize)]
struct Kyber768NISTKAT {
    #[serde(with = "hex::serde")]
    key_generation_seed: [u8; 64],

    #[serde(with = "hex::serde")]
    sha3_256_hash_of_public_key: [u8; 32],

    #[serde(with = "hex::serde")]
    sha3_256_hash_of_secret_key: [u8; 32],
}

#[test]
fn kyber768_known_answer_tests() {
    let katfile = File::open("tests/kyber768_nistkats.json").expect("Could not open KAT file.");
    let reader = BufReader::new(katfile);

    let nistkats: Vec<Kyber768NISTKAT> =
        serde_json::from_reader(reader).expect("Could not deserialize KAT file.");

    for kat in nistkats {
        let (pk_actual, sk_actual) = hacspec_kyber::generate_keypair(kat.key_generation_seed).unwrap();

        let pk_hash = digest::sha3_256(&pk_actual);
        for i in 0..pk_hash.len() {
            assert_eq!(pk_hash[i], kat.sha3_256_hash_of_public_key[i]);
        }

        let sk_hash = digest::sha3_256(&sk_actual);
        for i in 0..sk_hash.len() {
            assert_eq!(sk_hash[i], kat.sha3_256_hash_of_secret_key[i]);
        }
    }
}
