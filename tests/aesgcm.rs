#[cfg(not(target_arch = "wasm32"))]
use libcrux::drbg;
#[cfg(target_arch = "wasm32")]
use rand_core::OsRng;

use libcrux::{
    aead::{
        decrypt, encrypt, Aes128Key, Aes256Key,
        Algorithm::{Aes128Gcm, Aes256Gcm},
        EncryptError, InvalidArgumentError, Iv, Key,
    },
    aes_ni_support,
};

#[test]
fn aesgcm_self_test() {
    if !aes_ni_support() {
        eprintln!("AES not supported on this architecture.");
        return;
    }

    let _ = pretty_env_logger::try_init();

    let orig_msg = b"hacspec rulez";
    let mut msg = orig_msg.clone();
    let aad = b"associated data" as &[u8];
    let raw_key = Aes256Key([
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
        26, 27, 28, 29, 30, 31, 32,
    ]);
    let key = Key::Aes256(raw_key);
    let iv = Iv([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]);

    let tag = match encrypt(&key, &mut msg, iv, aad) {
        Ok(t) => t,
        Err(e) => {
            if matches!(
                e,
                EncryptError::InvalidArgument(InvalidArgumentError::UnsupportedAlgorithm)
            ) {
                eprintln!("AES not supported on this architecture.");
                return;
            } else {
                panic!("{:?}", e);
            }
        }
    };

    let iv = Iv([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]);
    assert!(decrypt(&key, &mut msg, iv, aad, &tag).is_ok());
    assert_eq!(orig_msg, &msg);

    let raw_key = Aes128Key([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]);
    let key = Key::Aes128(raw_key);
    let iv = Iv([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]);

    let tag = encrypt(&key, &mut msg, iv, aad).unwrap();

    let iv = Iv([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]);
    assert!(decrypt(&key, &mut msg, iv, aad, &tag).is_ok());
    assert_eq!(orig_msg, &msg);
}

#[test]
fn aesgcm_self_test_rand() {
    if !aes_ni_support() {
        eprintln!("AES not supported on this architecture.");
        return;
    }

    let _ = pretty_env_logger::try_init();

    let orig_msg = b"hacspec rulez";
    let mut msg = orig_msg.clone();
    let aad = b"associated data" as &[u8];

    #[cfg(not(target_arch = "wasm32"))]
    let mut rng = drbg::Drbg::new(libcrux::digest::Algorithm::Sha256).unwrap();
    #[cfg(target_arch = "wasm32")]
    let mut rng = OsRng;

    let key = Key::generate(Aes256Gcm, &mut rng);
    let iv = Iv::generate(&mut rng);
    let iv2 = Iv(iv.0);

    let tag = match encrypt(&key, &mut msg, iv, aad) {
        Ok(t) => t,
        Err(e) => {
            if matches!(
                e,
                EncryptError::InvalidArgument(InvalidArgumentError::UnsupportedAlgorithm)
            ) {
                eprintln!("AES not supported on this architecture.");
                return;
            } else {
                panic!("{:?}", e);
            }
        }
    };
    assert!(decrypt(&key, &mut msg, iv2, aad, &tag).is_ok());

    assert_eq!(orig_msg, &msg);

    let iv = Iv::generate(&mut rng);
    let iv2 = Iv(iv.0);
    let key = Key::generate(Aes128Gcm, &mut rng);
    let tag = encrypt(&key, &mut msg, iv, aad).unwrap();
    assert!(decrypt(&key, &mut msg, iv2, aad, &tag).is_ok());

    assert_eq!(orig_msg, &msg);
}
