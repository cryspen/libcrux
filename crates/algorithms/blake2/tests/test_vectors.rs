use libcrux_blake2::{Blake2bBuilder, Blake2sBuilder};

struct TestVector {
    key: Option<Vec<u8>>,
    input: Vec<u8>,
    hash: Vec<u8>,
}

fn parse_test_vectors(data: &str) -> Vec<TestVector> {
    let mut vectors = Vec::new();
    let mut key: Option<Vec<u8>> = None;
    let mut input: Option<Vec<u8>> = None;

    for line in data.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if let Some(rest) = line.strip_prefix("KEY:") {
            key = Some(hex::decode(rest.trim()).unwrap());
        } else if let Some(rest) = line.strip_prefix("IN:") {
            let rest = rest.trim();
            input = Some(if rest.is_empty() {
                vec![]
            } else {
                hex::decode(rest).unwrap()
            });
        } else if let Some(rest) = line.strip_prefix("HASH:") {
            let hash = hex::decode(rest.trim()).unwrap();
            vectors.push(TestVector {
                key: key.take(),
                input: input.take().expect("HASH without IN"),
                hash,
            });
        }
    }
    vectors
}

#[test]
fn blake2b256() {
    let data = include_str!("tv/blake2b256_tests.txt");
    let vectors = parse_test_vectors(data);
    assert!(!vectors.is_empty());

    for (i, tv) in vectors.iter().enumerate() {
        let mut got = [0u8; 32];
        if let Some(ref key) = tv.key {
            let mut hasher = Blake2bBuilder::new_keyed_dynamic(key)
                .unwrap()
                .build_var_digest_len(32)
                .unwrap();
            hasher.update(&tv.input).unwrap();
            hasher.finalize(&mut got).unwrap();
        } else {
            let mut hasher = Blake2bBuilder::new_unkeyed().build_const_digest_len();
            hasher.update(&tv.input).unwrap();
            hasher.finalize(&mut got);
        }
        assert_eq!(&got[..], &tv.hash[..], "blake2b256 vector {i} mismatch");
    }
    println!("Ran {} BLAKE2b-256 test vectors", vectors.len());
}

#[test]
fn blake2s256() {
    let data = include_str!("tv/blake2s256_tests.txt");
    let vectors = parse_test_vectors(data);
    assert!(!vectors.is_empty());

    for (i, tv) in vectors.iter().enumerate() {
        let mut got = [0u8; 32];
        if let Some(ref key) = tv.key {
            let mut hasher = Blake2sBuilder::new_keyed_dynamic(key)
                .unwrap()
                .build_var_digest_len(32)
                .unwrap();
            hasher.update(&tv.input).unwrap();
            hasher.finalize(&mut got).unwrap();
        } else {
            let mut hasher = Blake2sBuilder::new_unkeyed().build_const_digest_len();
            hasher.update(&tv.input).unwrap();
            hasher.finalize(&mut got);
        }
        assert_eq!(&got[..], &tv.hash[..], "blake2s256 vector {i} mismatch");
    }
    println!("Ran {} BLAKE2s-256 test vectors", vectors.len());
}
