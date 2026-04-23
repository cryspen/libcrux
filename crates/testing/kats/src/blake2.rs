pub struct TestVector {
    pub key: Option<Vec<u8>>,
    pub input: Vec<u8>,
    pub hash: Vec<u8>,
}

fn parse(data: &str) -> Vec<TestVector> {
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

pub fn load_blake2b256() -> Vec<TestVector> {
    parse(include_str!("tv/blake2b256_tests.txt"))
}

pub fn load_blake2s256() -> Vec<TestVector> {
    parse(include_str!("tv/blake2s256_tests.txt"))
}
