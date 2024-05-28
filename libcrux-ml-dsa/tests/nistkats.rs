use serde::Deserialize;
use serde_json;

use std::path::Path;

use std::{fs::File, io::BufReader};

#[derive(Debug, Deserialize)]
struct MlDsaNISTKAT {
    #[serde(with = "hex::serde")]
    key_generation_seed: [u8; 32],

    #[serde(with = "hex::serde")]
    sha3_256_hash_of_public_key: [u8; 32],

    #[serde(with = "hex::serde")]
    sha3_256_hash_of_secret_key: [u8; 32],

    // The length of the message in each KAT is 33 * (i + 1), where i is the
    // 0-indexed KAT counter.
    message: String,

    #[serde(with = "hex::serde")]
    sha3_256_hash_of_signature: [u8; 32],
}

#[ignore]
#[test]
fn ml_dsa_65_nist_known_answer_tests() {
    let katfile_path = Path::new("tests")
        .join("kats")
        .join(format!("nistkats-{}.json", 65));
    let katfile = File::open(katfile_path).expect("Could not open KAT file.");
    let reader = BufReader::new(katfile);

    let nist_kats: Vec<MlDsaNISTKAT> =
        serde_json::from_reader(reader).expect("Could not deserialize KAT file.");

    for kat in nist_kats {
        let _ = libcrux_ml_dsa::ml_dsa_65::generate_key_pair(kat.key_generation_seed);
    }
}
