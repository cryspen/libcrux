pub mod chacha20;
pub mod poly1305;

#[cfg(any(target_os = "linux", target_os = "macos"))]
pub mod sha2;

#[cfg(any(target_os = "linux", target_os = "macos"))]
pub mod sha3;

#[cfg(any(target_os = "linux", target_os = "macos"))]
pub mod x25519;

#[cfg(any(target_os = "linux", target_os = "macos"))]
pub mod kyber_derand;

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
