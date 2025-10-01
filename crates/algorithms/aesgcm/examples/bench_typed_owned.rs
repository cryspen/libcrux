// structs for typed_owned
use libcrux_aesgcm::{
    aes_gcm_128::{AesGcm128, Key, Nonce, Tag},
    AeadConsts as _,
};

fn main() {
    const PAYLOAD_SIZES: usize = 3045;

    let key: Key = [0x16; AesGcm128::KEY_LEN].into();
    let nonce: Nonce = [0x12; AesGcm128::NONCE_LEN].into();

    let aad = [0xff; 32];
    let plaintext = [0xab; PAYLOAD_SIZES];

    let mut ciphertext = vec![0; PAYLOAD_SIZES];
    let mut tag: Tag = [0u8; AesGcm128::TAG_LEN].into();

    for _ in 0..10000 {
        key.encrypt(&mut ciphertext, &mut tag, &nonce, &aad, &plaintext)
            .unwrap();
    }
}
