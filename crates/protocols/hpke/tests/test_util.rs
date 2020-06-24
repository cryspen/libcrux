#![allow(dead_code)]

use rand_core::{OsRng, RngCore};

pub(crate) fn random(l: usize) -> Vec<u8> {
    let mut r = vec![0u8; l];
    OsRng.fill_bytes(&mut r);
    r
}

pub(crate) fn bytes_to_hex(bytes: &[u8]) -> String {
    let mut hex = String::new();
    for &b in bytes {
        hex += &format!("{:02X}", b);
    }
    hex
}

pub(crate) fn hex_to_bytes(hex: &str) -> Vec<u8> {
    assert!(hex.len() % 2 == 0);
    let mut bytes = Vec::new();
    for i in 0..(hex.len() / 2) {
        bytes.push(u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).unwrap());
    }
    bytes
}

pub(crate) fn hex_to_bytes_option(hex: Option<String>) -> Vec<u8> {
    match hex {
        Some(s) => hex_to_bytes(&s),
        None => vec![],
    }
}

pub(crate) fn vec_to_option_slice<'a>(v: &'a Vec<u8>) -> Option<&'a[u8]> {
    if v.is_empty() {
        None
    } else {
        Some(&v[..])
    }
}
