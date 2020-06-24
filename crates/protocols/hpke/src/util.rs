#![allow(dead_code)]

use rand_core::{OsRng, RngCore};

#[inline]
pub(crate) fn concat(values: &[&[u8]]) -> Vec<u8> {
    values.join(&[][..])
}

pub(crate) fn random(l: usize) -> Vec<u8> {
    let mut r = vec![0u8; l];
    OsRng.fill_bytes(&mut r);
    r
}

#[inline]
pub(crate) fn xor_bytes(a: &[u8], b: &[u8]) -> Vec<u8> {
    assert_eq!(a.len(), b.len());
    a.iter().zip(b).map(|(x, y)| x ^ y).collect()
}

pub(crate) fn hex_to_bytes(hex: &str) -> Vec<u8> {
    assert!(hex.len() % 2 == 0);
    let mut bytes = Vec::new();
    for i in 0..(hex.len() / 2) {
        bytes.push(u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).unwrap());
    }
    bytes
}

pub(crate) fn bytes_to_hex(bytes: &[u8]) -> String {
    let mut hex = String::new();
    for &b in bytes {
        hex += &format!("{:02x}", b);
    }
    hex
}

#[test]
fn test_concat() {
    let a = "blabla";
    let b = "RFCXXXX ";
    let expected = "blablaRFCXXXX ";
    assert_eq!(
        expected.as_bytes()[..],
        concat(&[&a.as_bytes(), &b.as_bytes()])[..]
    )
}
