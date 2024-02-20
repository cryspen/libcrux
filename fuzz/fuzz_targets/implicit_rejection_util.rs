use libcrux::digest::shake256;

use libcrux::kem::PrivateKey;

use libcrux::kem::Ct;

use rand::Rng;

use rand::CryptoRng;

use libcrux::kem::Algorithm;

pub(crate) fn modify_ciphertext(
    alg: Algorithm,
    rng: &mut (impl CryptoRng + Rng),
    ciphertext: Ct,
) -> Ct {
    let mut raw_ciphertext = ciphertext.encode();

    let mut random_u32: usize = rng.next_u32().try_into().unwrap();

    let mut random_byte: u8 = (random_u32 & 0xFF) as u8;
    if random_byte == 0 {
        random_byte += 1;
    }
    random_u32 >>= 8;

    let position = random_u32 % raw_ciphertext.len();
    raw_ciphertext[position] ^= random_byte;

    Ct::decode(alg, &raw_ciphertext).unwrap()
}

pub(crate) const SHARED_SECRET_SIZE: usize = 32;

pub(crate) fn modify_secret_key(
    alg: Algorithm,
    rng: &mut (impl CryptoRng + Rng),
    secret_key: PrivateKey,
    modify_implicit_rejection_value: bool,
) -> PrivateKey {
    let mut raw_secret_key = secret_key.encode();

    let mut random_u32: usize = rng.next_u32().try_into().unwrap();

    let mut random_byte: u8 = (random_u32 & 0xFF) as u8;
    if random_byte == 0 {
        random_byte += 1;
    }
    random_u32 >>= 8;

    let position = if modify_implicit_rejection_value {
        (raw_secret_key.len() - SHARED_SECRET_SIZE) + (random_u32 % SHARED_SECRET_SIZE)
    } else {
        random_u32 % (raw_secret_key.len() - SHARED_SECRET_SIZE)
    };

    raw_secret_key[position] ^= random_byte;

    PrivateKey::decode(alg, &raw_secret_key).unwrap()
}

pub(crate) fn compute_implicit_rejection_shared_secret(
    ciphertext: Ct,
    secret_key: PrivateKey,
) -> [u8; SHARED_SECRET_SIZE] {
    let raw_secret_key = secret_key.encode();

    let mut to_hash = raw_secret_key[raw_secret_key.len() - SHARED_SECRET_SIZE..].to_vec();
    to_hash.extend_from_slice(&ciphertext.encode());

    shake256(&to_hash)
}
