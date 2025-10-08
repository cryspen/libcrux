use wycheproof::{aead::Test, TestResult};

fn run<Cipher: libcrux_aesgcm::Aead>(test: &Test, cipher: Cipher) {
    let mut ciphertext = vec![0u8; test.pt.len()];
    let mut plaintext = vec![0u8; test.pt.len()];
    let mut tag_bytes = [0u8; 16];

    let key = cipher.new_key(&test.key).unwrap();
    let nonce = cipher.new_nonce(&test.nonce).unwrap();
    let tag = cipher.new_tag_mut(&mut tag_bytes).unwrap();

    key.encrypt(&mut ciphertext, tag, nonce, &test.aad, &test.pt)
        .unwrap();

    let tag = cipher.new_tag(&tag_bytes).unwrap();
    key.decrypt(&mut plaintext, nonce, &test.aad, &ciphertext, tag)
        .unwrap();

    assert_eq!(plaintext.as_slice(), test.pt.as_slice());

    if test.result == TestResult::Valid {
        assert_eq!(test.ct.as_slice(), &ciphertext);
        assert_eq!(test.tag.as_slice(), tag.as_ref());
    } else {
        let ct_ok = test.ct.as_slice() == ciphertext;
        let tag_ok = test.tag.as_slice() == tag.as_ref();
        assert!(!ct_ok || !tag_ok);
    }
}

fn test_variant(cipher: impl libcrux_aesgcm::Aead) {
    let test_set = wycheproof::aead::TestSet::load(wycheproof::aead::TestName::AesGcm).unwrap();

    // Ensure we ran some tests.
    let mut tested = false;

    for test_group in test_set.test_groups {
        println!(
            "* Group key size:{} tag size:{} nonce size:{}",
            test_group.key_size, test_group.tag_size, test_group.nonce_size,
        );

        if test_group.nonce_size != 96 {
            println!("  Skipping unsupported nonce size");
            continue;
        }

        if test_group.key_size / 8 == cipher.key_len() {
            for test in test_group.tests {
                run(&test, cipher);
                tested = true;
            }
        }
    }

    assert!(tested, "No tests were run.")
}

#[test]
fn aes128() {
    // Multiplexing
    test_variant(libcrux_aesgcm::AesGcm128);
}

#[test]
fn aes128_portable() {
    test_variant(libcrux_aesgcm::aes_gcm_128::portable::PortableAesGcm128);
}

#[cfg(feature = "simd128")]
#[test]
fn aes128_neon() {
    test_variant(libcrux_aesgcm::aes_gcm_128::neon::NeonAesGcm128);
}

#[cfg(feature = "simd256")]
#[test]
fn aes128_x64() {
    test_variant(libcrux_aesgcm::aes_gcm_128::x64::X64AesGcm128);
}

#[test]
fn aes256() {
    // Multiplexing
    test_variant(libcrux_aesgcm::AesGcm256);
}

#[test]
fn aes256_portable() {
    test_variant(libcrux_aesgcm::aes_gcm_256::portable::PortableAesGcm256);
}

#[cfg(feature = "simd128")]
#[test]
fn aes256_neon() {
    test_variant(libcrux_aesgcm::aes_gcm_256::neon::NeonAesGcm256);
}

#[cfg(feature = "simd256")]
#[test]
fn aes256_x64() {
    test_variant(libcrux_aesgcm::aes_gcm_256::x64::X64AesGcm256);
}
