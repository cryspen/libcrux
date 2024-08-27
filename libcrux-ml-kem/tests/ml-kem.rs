//! Tests for ML-KEM

/// These tests are from https://github.com/C2SP/CCTV/
#[allow(dead_code)]
fn test_invalid_modulus(p: &str) {
    use std::{
        fs::File,
        io::{BufRead, BufReader},
    };

    let kat_file_path = file_name(p);
    let kat_file = File::open(kat_file_path).unwrap();
    let reader = BufReader::new(kat_file);
    for line in reader.lines() {
        let line = line.unwrap();
        let pk = hex::decode(line).unwrap();
        let pk = pk.as_slice();
        match p {
            #[cfg(all(feature = "mlkem512", feature = "pre-verification"))]
            "512" => assert!(!libcrux_ml_kem::mlkem512::validate_public_key(
                &pk.try_into().unwrap()
            )),
            #[cfg(all(feature = "mlkem768", feature = "pre-verification"))]
            "768" => assert!(!libcrux_ml_kem::mlkem768::validate_public_key(
                &pk.try_into().unwrap()
            )),
            #[cfg(all(feature = "mlkem1024", feature = "pre-verification"))]
            "1024" => assert!(!libcrux_ml_kem::mlkem1024::validate_public_key(
                &pk.try_into().unwrap()
            )),
            _ => unreachable!(),
        };
    }
}

#[test]
#[cfg(all(feature = "mlkem512", feature = "pre-verification"))]
fn invalid_modulus_512() {
    test_invalid_modulus("512");
}

#[test]
#[cfg(all(feature = "mlkem768", feature = "pre-verification"))]
fn invalid_modulus_768() {
    test_invalid_modulus("768");
}

#[test]
#[cfg(all(feature = "mlkem1024", feature = "pre-verification"))]
fn invalid_modulus_1024() {
    test_invalid_modulus("1024");
}

fn file_name(p: &str) -> std::path::PathBuf {
    std::path::Path::new("tests")
        .join("kats")
        .join("invalid_modulus")
        .join(format!("ML-KEM-{}.txt", p))
}
