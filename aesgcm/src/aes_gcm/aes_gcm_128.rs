use crate::{
    aes_ctr::{
        aes128_ctr_init, aes128_ctr_key_block, aes128_ctr_set_nonce, aes128_ctr_update,
        Aes128CtrContext,
    },
    gf128_generic::{gf128_emit, gf128_init, gf128_update, gf128_update_padded, GF128State},
    platform::{AESState, GF128FieldElement},
};

#[allow(non_camel_case_types)]
pub(crate) struct AES128_GCM_State<T: AESState, U: GF128FieldElement> {
    pub(crate) aes_state: Aes128CtrContext<T>,
    pub(crate) gcm_state: GF128State<U>,
    pub(crate) tag_mix: [u8; 16],
}

pub(crate) fn aes128_gcm_init<T: AESState, U: GF128FieldElement>(
    key: &[u8],
) -> AES128_GCM_State<T, U> {
    debug_assert!(key.len() == 16);

    let nonce = [0u8; 12];
    let mut gcm_key = [0u8; 16];
    let tag_mix = [0u8; 16];

    let aes_state = aes128_ctr_init(key, &nonce);
    aes128_ctr_key_block(&aes_state, 0, &mut gcm_key);
    let gcm_state = gf128_init(&gcm_key);

    AES128_GCM_State {
        aes_state,
        gcm_state,
        tag_mix,
    }
}

pub(crate) fn aes128_gcm_set_nonce<T: AESState, U: GF128FieldElement>(
    st: &mut AES128_GCM_State<T, U>,
    nonce: &[u8],
) {
    debug_assert!(nonce.len() == 12);

    aes128_ctr_set_nonce(&mut st.aes_state, nonce);
    aes128_ctr_key_block(&st.aes_state, 1, &mut st.tag_mix);
}

pub(crate) fn aes128_gcm_encrypt<T: AESState, U: GF128FieldElement>(
    st: &mut AES128_GCM_State<T, U>,
    aad: &[u8],
    plaintext: &[u8],
    ciphertext: &mut [u8],
    tag: &mut [u8],
) {
    debug_assert!(ciphertext.len() == plaintext.len());
    debug_assert!(plaintext.len() / 16 <= u32::MAX as usize);
    debug_assert!(tag.len() == 16);

    aes128_ctr_update(&st.aes_state, 2, plaintext, ciphertext);

    gf128_update_padded(&mut st.gcm_state, aad);
    gf128_update_padded(&mut st.gcm_state, ciphertext);

    let mut last_block = [0u8; 16];
    last_block[0..8].copy_from_slice(&((aad.len() as u64) * 8).to_be_bytes());
    last_block[8..16].copy_from_slice(&((plaintext.len() as u64) * 8).to_be_bytes());

    gf128_update(&mut st.gcm_state, &last_block);
    gf128_emit(&st.gcm_state, tag);

    for i in 0..16 {
        tag[i] ^= st.tag_mix[i];
    }
}

/// AES-GCM decryption error.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DecryptError();

pub(crate) fn aes128_gcm_decrypt<T: AESState, U: GF128FieldElement>(
    st: &mut AES128_GCM_State<T, U>,
    aad: &[u8],
    ciphertext: &[u8],
    tag: &[u8],
    plaintext: &mut [u8],
) -> Result<(), DecryptError> {
    debug_assert!(plaintext.len() == ciphertext.len());
    debug_assert!(ciphertext.len() / 16 <= u32::MAX as usize);
    debug_assert!(tag.len() == 16);

    gf128_update_padded(&mut st.gcm_state, aad);
    gf128_update_padded(&mut st.gcm_state, ciphertext);

    let mut last_block = [0u8; 16];
    last_block[0..8].copy_from_slice(&((aad.len() as u64) * 8).to_be_bytes());
    last_block[8..16].copy_from_slice(&((plaintext.len() as u64) * 8).to_be_bytes());

    gf128_update(&mut st.gcm_state, &last_block);

    let mut computed_tag = [0u8; 16];
    gf128_emit(&st.gcm_state, &mut computed_tag);
    for i in 0..16 {
        computed_tag[i] ^= st.tag_mix[i];
    }
    let mut eq_mask = 0u8;
    for i in 0..16 {
        eq_mask |= computed_tag[i] ^ tag[i];
    }
    if eq_mask == 0 {
        aes128_ctr_update(&st.aes_state, 2, ciphertext, plaintext);
        Ok(())
    } else {
        Err(DecryptError())
    }
}
