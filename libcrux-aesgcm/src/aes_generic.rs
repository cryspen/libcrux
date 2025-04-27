use crate::platform::*;

pub(crate) type ExtendedKey<T, const NUM_KEYS: usize> = [T; NUM_KEYS];

const RCON: [u8; 11] = [
    0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36,
];

pub(crate) fn aes128_key_expansion<T: AESState>(key: &[u8]) -> ExtendedKey<T, 11> {
    debug_assert!(key.len() == 16);
    let mut keyex = [T::new(); 11];
    keyex[0].load_block(&key);

    macro_rules! expansion_step128 {
        ($i:expr,$rcon:expr) => {
            let prev = keyex[$i-1];
            keyex[$i].aes_keygen_assist0::<$rcon>(&prev);
            keyex[$i].key_expansion_step(&prev);
        }
    }
    expansion_step128!(1,0x01);
    expansion_step128!(2,0x02);
    expansion_step128!(3,0x04);
    expansion_step128!(4,0x08);
    expansion_step128!(5,0x10);
    expansion_step128!(6,0x20);
    expansion_step128!(7,0x40);
    expansion_step128!(8,0x80);
    expansion_step128!(9,0x1b);
    expansion_step128!(10,0x36);
    keyex
}

pub(crate) fn aes256_key_expansion<T: AESState>(key: &[u8]) -> ExtendedKey<T, 15> {
    debug_assert!(key.len() == 32);
    let mut keyex = [T::new(); 15];
    keyex[0].load_block(&key[0..16]);
    keyex[1].load_block(&key[16..32]);

    macro_rules! expansion_step256 {
        ($i:expr,$rcon:expr) => {
            let prev0 = keyex[$i-2];
            let prev1 = keyex[$i-1];
            keyex[$i].aes_keygen_assist0::<$rcon>(&prev1);
            keyex[$i].key_expansion_step(&prev0);
            let next0 = keyex[$i];
            keyex[$i+1].aes_keygen_assist1(&next0);
            keyex[$i+1].key_expansion_step(&prev1);
        }
    }

    expansion_step256!(2,0x01);
    expansion_step256!(3,0x01);
    expansion_step256!(4,0x02);
    expansion_step256!(5,0x02);
    expansion_step256!(6,0x04);
    expansion_step256!(7,0x04);
    expansion_step256!(8,0x08);
    expansion_step256!(9,0x08);
    expansion_step256!(10,0x10);
    expansion_step256!(11,0x10);
    expansion_step256!(12,0x20);
    expansion_step256!(13,0x20);

    let prev0 = keyex[12];
    let prev1 = keyex[13];
    keyex[14].aes_keygen_assist0::<0x40>(&prev1);
    keyex[14].key_expansion_step(&prev0);
    keyex
}

pub(crate) fn block_cipher<T: AESState, const NUM_KEYS: usize>(
    st: &mut T,
    keyex: ExtendedKey<T, NUM_KEYS>,
) {
    st.xor_key(&keyex[0]);
    for i in 1..NUM_KEYS - 1 {
        st.aes_enc(&keyex[i]);
    }
    st.aes_enc_last(&keyex[NUM_KEYS - 1]);
}
