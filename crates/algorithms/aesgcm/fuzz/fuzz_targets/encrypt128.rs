#![no_main]

use libcrux_aesgcm::Aead;

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if data.len() < 16 + 12 + 7 {
        // We want at least a key, nonce, and a few input bytes.
        return;
    }

    let key = &data[0..16];
    let nonce = &data[16..16 + 12];
    let aad = &data[16 + 12..16 + 12 + 5];

    let mut ctxt = vec![0u8; data.len()];
    let mut tag_bytes = [0u8; 16];
    let algo = libcrux_aesgcm::PortableAesGcm128;

    let key = algo.new_key(key).unwrap();
    let nonce = algo.new_nonce(nonce).unwrap();
    let tag = algo.new_tag_mut(&mut tag_bytes).unwrap();

    key.encrypt(&mut ctxt, tag, nonce, &aad, &data).unwrap();
});
