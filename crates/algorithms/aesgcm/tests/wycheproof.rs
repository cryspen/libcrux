use wycheproof::{aead::Test, TestResult};

#[test]
fn test() {
    let test_set = wycheproof::aead::TestSet::load(wycheproof::aead::TestName::AesGcm).unwrap();

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

    for test_group in test_set.test_groups {
        println!(
            "* Group key size:{} tag size:{} nonce size:{}",
            test_group.key_size, test_group.tag_size, test_group.nonce_size,
        );

        if test_group.nonce_size != 96 {
            println!("  Skipping unsupported nonce size");
            continue;
        }

        if test_group.key_size == 128 {
            for test in test_group.tests {
                println!("  Test AES-GCM 128 {}", test.tc_id);

                // Multiplexing
                run(&test, libcrux_aesgcm::AesGcm128 {});

                // Portable
                run(&test, libcrux_aesgcm::PortableAesGcm128 {});

                // Neon
                #[cfg(feature = "simd128")]
                run(&test, libcrux_aesgcm::NeonAesGcm128 {});

                // x64
                #[cfg(feature = "simd256")]
                run(&test, libcrux_aesgcm::X64AesGcm128 {});
            }
        } else if test_group.key_size == 256 {
            for test in test_group.tests {
                println!("  Test AES-GCM 256 {}", test.tc_id);

                // Multiplexing
                run(&test, libcrux_aesgcm::AesGcm256 {});

                // Portable
                run(&test, libcrux_aesgcm::PortableAesGcm256 {});

                // Neon
                #[cfg(feature = "simd128")]
                run(&test, libcrux_aesgcm::NeonAesGcm256 {});

                // x64
                #[cfg(feature = "simd256")]
                run(&test, libcrux_aesgcm::X64AesGcm256 {});
            }
        }
    }
}
