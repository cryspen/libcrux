//! #Libjade Rust bindings

mod bindings;
pub use bindings::*;

#[cfg(not(simd256))]
pub unsafe fn jade_hash_sha3_256_amd64_avx2(
    _: *mut u8,
    _: *mut u8,
    _: u64,
) -> ::std::os::raw::c_int {
    panic!("No AVX2 support comiled. Use --cfg simd256 to enable it.")
}

// ===

#[cfg(test)]
mod tests {
    use super::*;
    use std::fmt::Write;

    type Sha256Digest = [u8; 32];

    fn sha256(input: &[u8]) -> Result<Sha256Digest, &'static str> {
        let mut digest = Sha256Digest::default();
        let r = unsafe {
            jade_hash_sha256_amd64_ref(
                digest.as_mut_ptr(),
                input.as_ptr() as _,
                input.len().try_into().unwrap(),
            )
        };
        if r != 0 {
            Err("Error while hashing.")
        } else {
            Ok(digest)
        }
    }

    type Curve25519Point = [u8; 32];

    fn x25519_cpu_support() -> bool {
        std::arch::is_x86_feature_detected!("bmi2") && std::arch::is_x86_feature_detected!("adx")
    }

    fn x25519(scalar: &[u8], point: &[u8]) -> Result<Curve25519Point, &'static str> {
        let mut result = Curve25519Point::default();
        let r = if x25519_cpu_support() {
            log::trace!("Jasmin x25519 mulx");
            unsafe {
                jade_scalarmult_curve25519_amd64_mulx(
                    result.as_mut_ptr(),
                    scalar.as_ptr() as _,
                    point.as_ptr() as _,
                )
            }
        } else {
            log::trace!("Jasmin x25519 ref");
            unsafe {
                jade_scalarmult_curve25519_amd64_ref5(
                    result.as_mut_ptr(),
                    scalar.as_ptr() as _,
                    point.as_ptr() as _,
                )
            }
        };
        if r != 0 {
            Err("Error while computing x25519.")
        } else {
            Ok(result)
        }
    }

    fn x25519_base(scalar: &[u8]) -> Result<Curve25519Point, &'static str> {
        let mut result = Curve25519Point::default();
        let base = [
            0x09u8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
        ];

        let r = if x25519_cpu_support() {
            log::trace!("Jasmin x25519 mulx");
            unsafe {
                jade_scalarmult_curve25519_amd64_mulx(
                    result.as_mut_ptr(),
                    scalar.as_ptr() as _,
                    base.as_ptr() as _,
                )
            }
        } else {
            log::trace!("Jasmin x25519 ref");
            unsafe {
                jade_scalarmult_curve25519_amd64_ref5(
                    result.as_mut_ptr(),
                    scalar.as_ptr() as _,
                    base.as_ptr() as _,
                )
            }
        };
        if r != 0 {
            Err("Error while computing x25519.")
        } else {
            Ok(result)
        }
    }

    fn bytes_to_hex(bytes: &[u8]) -> String {
        let mut s = String::with_capacity(2 * bytes.len());
        for byte in bytes {
            write!(s, "{:02x}", byte).unwrap();
        }
        s
    }

    #[test]
    fn hashit() {
        let _ = pretty_env_logger::try_init();

        let input = b"jasmin rulez" as &[u8];
        let digest = sha256(input).unwrap();

        println!("{:x?}", digest);
        let expected = "16096ecad8aa127418804b21c8e2fe93c31453d66a7e9588a429813c968bddd1";
        assert_eq!(expected, bytes_to_hex(&digest));
    }

    #[test]
    fn x25519_test() {
        let _ = pretty_env_logger::try_init();

        let public = [
            0x50, 0x4a, 0x36, 0x99, 0x9f, 0x48, 0x9c, 0xd2, 0xfd, 0xbc, 0x08, 0xba, 0xff, 0x3d,
            0x88, 0xfa, 0x00, 0x56, 0x9b, 0xa9, 0x86, 0xcb, 0xa2, 0x25, 0x48, 0xff, 0xde, 0x80,
            0xf9, 0x80, 0x68, 0x29,
        ];
        let private = [
            0xc8, 0xa9, 0xd5, 0xa9, 0x10, 0x91, 0xad, 0x85, 0x1c, 0x66, 0x8b, 0x07, 0x36, 0xc1,
            0xc9, 0xa0, 0x29, 0x36, 0xc0, 0xd3, 0xad, 0x62, 0x67, 0x08, 0x58, 0x08, 0x80, 0x47,
            0xba, 0x05, 0x74, 0x75,
        ];
        let shared = x25519(&private, &public).unwrap();

        println!("{:x?}", shared);
        let expected = "436a2c040cf45fea9b29a0cb81b1f41458f863d0d61b453d0a982720d6d61320";
        assert_eq!(expected, bytes_to_hex(&shared));

        let _s = x25519_base(&private).unwrap();
    }
}
