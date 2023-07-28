//! #Libjade Rust bindings

mod bindings;
pub use bindings::*;

// Function definitions for things not compiled in certain configurations.
mod fallback_definitions;
pub use fallback_definitions::*;

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

    type Kyber768PublicKey = [u8; 1184];
    type Kyber768SecretKey = [u8; 2400];

    type Kyber768KeypairSeed = [u8; 64];

    struct Kyber768Keypair {
        public_key : Kyber768PublicKey,
        secret_key : Kyber768SecretKey
    }

    fn kyber768_keypair_derand(seed : Kyber768KeypairSeed) -> Result<Kyber768Keypair, &'static str> {
        let mut public_key : Kyber768PublicKey = [0; 1184];
        let mut secret_key : Kyber768SecretKey = [0; 2400];

        log::trace!("Jasmin kyber768 ref");
        let r = unsafe {
            jade_kem_kyber_kyber768_amd64_ref_keypair_derand(
                public_key.as_mut_ptr(),
                secret_key.as_mut_ptr(),
                seed.as_ptr() as _,
            )
        };

        if r != 0 {
            Err("Error while running kyber768 keypair().")
        } else {
            Ok(Kyber768Keypair { public_key, secret_key })
        }
    }

    type Kyber768Ciphertext = [u8; 1088];
    type Kyber768SharedSecret = [u8; 32];

    type Kyber768EncSeed = [u8; 32];

    fn kyber768_enc_derand(public_key : Kyber768PublicKey, seed : Kyber768EncSeed) -> Result<(Kyber768Ciphertext, Kyber768SharedSecret), &'static str> {
        let mut ciphertext : Kyber768Ciphertext = [0; 1088];
        let mut shared_secret : Kyber768SharedSecret = [0; 32];

        log::trace!("Jasmin kyber768 enc");
        let r = unsafe {
            jade_kem_kyber_kyber768_amd64_ref_enc_derand(
                ciphertext.as_mut_ptr(),
                shared_secret.as_mut_ptr(),
                public_key.as_ptr() as _,
                seed.as_ptr() as _,
            )
        };

        if r != 0 {
            Err("Error while running kyber768 keypair().")
        } else {
            Ok((ciphertext, shared_secret))
        }
    }

    fn kyber768_dec(ciphertext : Kyber768Ciphertext, secret_key : Kyber768SecretKey) -> Result<Kyber768SharedSecret, &'static str> {
        let mut shared_secret : Kyber768SharedSecret = [0; 32];

        log::trace!("Jasmin kyber768 dec");
        let r = unsafe {
            jade_kem_kyber_kyber768_amd64_ref_dec(
                shared_secret.as_mut_ptr(),
                ciphertext.as_ptr() as _,
                secret_key.as_ptr() as _,
            )
        };

        if r != 0 {
            Err("Error while running kyber768 keypair().")
        } else {
            Ok(shared_secret)
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

    #[test]
    fn kyber768_consistency_test() {
        let _ = pretty_env_logger::try_init();

        let keypair_seed = [0u8; 64];
        let enc_seed = [0u8; 32];

        let keypair = kyber768_keypair_derand(keypair_seed).unwrap();

        let (ciphertext, shared_secret) = kyber768_enc_derand(keypair.public_key, enc_seed).unwrap();

        let shared_secret_decapsulated = kyber768_dec(ciphertext, keypair.secret_key).unwrap();

        assert_eq!(shared_secret_decapsulated, shared_secret);
    }
}
