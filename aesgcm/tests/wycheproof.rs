use libcrux_traits::aead::Aead;
use wycheproof::{aead::Test, TestResult};

#[test]
fn test() {
    let test_set = wycheproof::aead::TestSet::load(wycheproof::aead::TestName::AesGcm).unwrap();

    fn run<Cipher: Aead<Tag = [u8; 16], Key = [u8; 16], Nonce = [u8; 12]>>(test: &Test) {
        let mut ciphertext = vec![0u8; test.pt.len()];
        let mut plaintext = vec![0u8; test.pt.len()];
        let mut tag = [0u8; 16];

        Cipher::encrypt(
            &mut ciphertext,
            &mut tag,
            test.key.as_ref().try_into().unwrap(),
            test.nonce.as_ref().try_into().unwrap(),
            &test.aad,
            &test.pt,
        )
        .unwrap();
        Cipher::decrypt(
            &mut plaintext,
            test.key.as_ref().try_into().unwrap(),
            test.nonce.as_ref().try_into().unwrap(),
            &test.aad,
            &ciphertext,
            tag.as_ref().try_into().unwrap(),
        )
        .unwrap();

        assert_eq!(plaintext.as_slice(), test.pt.as_slice());

        if test.result == TestResult::Valid {
            assert_eq!(test.ct.as_slice(), &ciphertext);
            assert_eq!(test.tag.as_slice(), &tag);
        } else {
            let ct_ok = test.ct.as_slice() == &ciphertext;
            let tag_ok = test.tag.as_slice() == &tag;
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
                println!("  Test {}", test.tc_id);
                // Multiplexing
                run::<libcrux_aesgcm::AesGcm128>(&test);

                // Portable
                run::<libcrux_aesgcm::PortableAesGcm128>(&test);

                // Neon
                #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
                run::<libcrux_aesgcm::NeonAesGcm128>(&test);

                // x64
                #[cfg(all(target_arch = "x86_64"))]
                run::<libcrux_aesgcm::X64AesGcm128>(&test);
            }
        } else if test_group.key_size == 256 {
            for _test in test_group.tests {
                // TODO
            }
        }
    }
}
