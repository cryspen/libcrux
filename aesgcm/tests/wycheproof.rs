use wycheproof::TestResult;

#[test]
fn test() {
    let test_set = wycheproof::aead::TestSet::load(wycheproof::aead::TestName::AesGcm).unwrap();

    macro_rules! run {
        ($encrypt:expr, $decrypt:expr, $test:expr, $key:expr, $nonce:expr, $aad:expr, $pt:expr) => {
            let mut ciphertext = vec![0u8; $pt.len()];
            let mut plaintext = vec![0u8; $pt.len()];
            let mut tag = [0u8; 16];

            $encrypt($key, $nonce, $aad, $pt, &mut ciphertext, &mut tag);
            $decrypt($key, $nonce, $aad, &ciphertext, &tag, &mut plaintext).unwrap();

            assert_eq!(plaintext.as_slice(), $pt.as_slice());

            if $test.result == TestResult::Valid {
                assert_eq!($test.ct.as_slice(), &ciphertext);
                assert_eq!($test.tag.as_slice(), &tag);
            } else {
                let ct_ok = $test.ct.as_slice() == &ciphertext;
                let tag_ok = $test.tag.as_slice() == &tag;
                assert!(!ct_ok || !tag_ok);
            }
        };
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
                println!("  Test {}", test.tc_id);
                run!(
                    libcrux_aesgcm::portable::aes128_gcm_encrypt,
                    libcrux_aesgcm::portable::aes128_gcm_decrypt,
                    test,
                    &test.key,
                    &test.nonce,
                    &test.aad,
                    &test.pt
                );

                #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
                run!(
                    libcrux_aesgcm::neon::aes128_gcm_encrypt,
                    libcrux_aesgcm::neon::aes128_gcm_decrypt,
                    test,
                    &test.key,
                    &test.nonce,
                    &test.aad,
                    &test.pt
                );

                #[cfg(all(target_arch = "x86_64"))]
                run!(
                    libcrux_aesgcm::intel_ni::aes128_gcm_encrypt,
                    libcrux_aesgcm::intel_ni::aes128_gcm_decrypt,
                    test,
                    &test.key,
                    &test.nonce,
                    &test.aad,
                    &test.pt
                );
            }
        } else if test_group.key_size == 256 {
            for _test in test_group.tests {
                // TODO
            }
        }
    }
}
