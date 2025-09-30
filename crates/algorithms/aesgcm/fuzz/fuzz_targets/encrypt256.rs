#![no_main]

use libcrux_aesgcm::Aead;

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if data.len() < 32 + 12 + 7 {
        // We want at least a key, nonce, and a few input bytes.
        return;
    }

    let key = &data[0..32];
    let nonce = &data[32..32 + 12];
    let aad = &data[32 + 12..32 + 12 + 5];

    let mut ctxt = vec![0u8; data.len()];
    let mut tag_bytes = [0u8; 16];
    let algo = libcrux_aesgcm::PortableAesGcm256;

    let key = algo.new_key(key).unwrap();
    let nonce = algo.new_nonce(nonce).unwrap();
    let tag = algo.new_tag_mut(&mut tag_bytes).unwrap();

    key.encrypt(&mut ctxt, tag, nonce, &aad, &data).unwrap();
});
