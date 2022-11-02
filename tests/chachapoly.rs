use libcrux::aead::{decrypt, encrypt, Algorithm::Chacha20Poly1305, Key};

#[test]
fn chachapoly_self_test() {
    let _ = pretty_env_logger::try_init();

    let orig_msg = b"hacspec rulez";
    let mut msg = orig_msg.clone();
    let aad = b"associated data" as &[u8];
    let key = Key::Chacha20Poly1305([
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
        26, 27, 28, 29, 30, 31, 32,
    ]);
    let iv = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12];

    let tag = encrypt(Chacha20Poly1305, &key, &mut msg, &iv, aad).unwrap();
    assert!(decrypt(Chacha20Poly1305, &key, &mut msg, &iv, aad, &tag).is_ok());
    assert_eq!(orig_msg, &msg);
}
