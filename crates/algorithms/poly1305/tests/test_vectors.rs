fn hex_to_bytes(hex: &str) -> Vec<u8> {
    (0..hex.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).unwrap())
        .collect()
}

struct TestVector {
    key: [u8; 32],
    input: Vec<u8>,
    mac: [u8; 16],
}

fn parse_test_vectors(data: &str) -> Vec<TestVector> {
    let mut vectors = Vec::new();
    let mut key: Option<[u8; 32]> = None;
    let mut input: Option<Vec<u8>> = None;

    for line in data.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if let Some(rest) = line.strip_prefix("Key =") {
            let bytes = hex_to_bytes(rest.trim());
            key = Some(bytes.try_into().expect("key must be 32 bytes"));
        } else if let Some(rest) = line.strip_prefix("Input =") {
            let rest = rest.trim();
            input = Some(if rest.is_empty() {
                vec![]
            } else {
                hex_to_bytes(rest)
            });
        } else if let Some(rest) = line.strip_prefix("MAC =") {
            let mac_bytes = hex_to_bytes(rest.trim());
            vectors.push(TestVector {
                key: key.take().expect("MAC without Key"),
                input: input.take().expect("MAC without Input"),
                mac: mac_bytes.try_into().expect("mac must be 16 bytes"),
            });
        }
    }
    vectors
}

#[test]
fn poly1305_test_vectors() {
    let data = include_str!("tv/poly1305_tests.txt");
    let vectors = parse_test_vectors(data);
    assert!(!vectors.is_empty());

    for (i, tv) in vectors.iter().enumerate() {
        let mut tag = [0u8; 16];
        libcrux_poly1305::mac(&tv.key, &tv.input, &mut tag)
            .unwrap_or_else(|_| panic!("vector {i}: mac failed"));
        assert_eq!(&tag, &tv.mac, "vector {i}: MAC mismatch");
    }
    println!("Ran {} Poly1305 test vectors", vectors.len());
}
