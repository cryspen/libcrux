//! Tests for ML-KEM

use std::{
    fs::File,
    io::{BufRead, BufReader},
    path::Path,
};

use libcrux_ml_kem::{kyber1024, kyber512, kyber768};

/// These tests are from https://github.com/C2SP/CCTV/
fn test_invalid_modulus(p: &str) {
    let kat_file_path = file_name(p);
    let kat_file = File::open(kat_file_path).unwrap();
    let reader = BufReader::new(kat_file);
    for line in reader.lines() {
        let line = line.unwrap();
        let pk = hex::decode(line).unwrap();
        let pk = pk.as_slice();
        match p {
            "512" => assert!(kyber512::validate_public_key(pk.try_into().unwrap()).is_none()),
            "768" => assert!(kyber768::validate_public_key(pk.try_into().unwrap()).is_none()),
            "1024" => assert!(kyber1024::validate_public_key(pk.try_into().unwrap()).is_none()),
            _ => unreachable!(),
        };
    }
}

#[test]
fn invalid_modulus_512() {
    test_invalid_modulus("512");
}

#[test]
fn invalid_modulus_768() {
    test_invalid_modulus("768");
}

#[test]
fn invalid_modulus_1024() {
    test_invalid_modulus("1024");
}

fn file_name(p: &str) -> std::path::PathBuf {
    Path::new("tests")
        .join("kats")
        .join("invalid_modulus")
        .join(format!("ML-KEM-{}.txt", p))
}
