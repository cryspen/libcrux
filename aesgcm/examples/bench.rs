use libcrux_aesgcm::Aead;

fn main() {
    const PAYLOAD_SIZES: usize = 3045;

    let key = [0x16; 16];
    let nonce = [0x12; 12];

    let aad = [0xff; 32];
    let plaintext = [0xab; PAYLOAD_SIZES];

    let mut ciphertext = vec![0; PAYLOAD_SIZES];
    let mut tag = [0u8; 16];

    for _ in 0..10000 {
        libcrux_aesgcm::AesGcm128::encrypt(
            &mut ciphertext,
            &mut tag,
            &key,
            &nonce,
            &aad,
            &plaintext,
        )
        .unwrap();
    }
}
