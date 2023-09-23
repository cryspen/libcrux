pub mod chacha20;
pub mod kyber_derand;
pub mod poly1305;
pub mod sha2;
pub mod sha3;
pub mod x25519;

#[cfg(test)]
mod testing {
    use std::fmt::Write;

    pub(crate) fn bytes_to_hex(bytes: &[u8]) -> String {
        let mut s = String::with_capacity(2 * bytes.len());
        for byte in bytes {
            write!(s, "{:02x}", byte).unwrap();
        }
        s
    }
}
