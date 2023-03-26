use std::fmt::Write;

fn bytes_to_hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(2 * bytes.len());
    for byte in bytes {
        write!(s, "{:02x}", byte).unwrap();
    }
    s
}

#[test]
fn sha256_kat() {
    let mut digest = libcrux::digest::Sha2_256::new();
    digest.update(b"libcrux sha2 256 tests");
    let d = digest.finish();

    let expected = "8683520e19e5b33db33c8fb90918c0c96fcdfd9a17c695ce0f0ea2eaa0c95956";
    assert_eq!(bytes_to_hex(&d), expected);
}
