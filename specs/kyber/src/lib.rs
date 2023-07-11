mod parameters;
mod field;
mod ring;
mod bit_vector;
mod sampling;
mod encoding;
mod ind_cpa;

use libcrux::digest;

pub const KYBER768_KEYGEN_SEED_BYTES : usize = 64;
pub const KYBER768_PUBLIC_KEY_BYTES : usize = 1184;
pub const KYBER768_SECRET_KEY_BYTES : usize = 2400;

pub fn keygen(seed : [u8; 64]) -> ([u8; 1184], [u8; 2400]) {
    let (pk, sk_indcpa) = ind_cpa::key_gen(&seed[0..32]);
    let mut sk : [u8; 2400] = [0; 2400];

    let pk_hash = digest::sha3_256(&pk);

    for i in 0..sk_indcpa.len() {
        sk[i] = sk_indcpa[i];
    }
    for i in 0..pk.len() {
        sk[sk_indcpa.len() + i] = pk[i];
    }
    for i in 0..pk_hash.len() {
        sk[sk_indcpa.len() + pk.len() + i] = pk_hash[i];
    }
    for i in 0..32 {
        sk[sk_indcpa.len() + pk.len() + pk_hash.len() + i] = seed[32 + i];
    }

    (pk, sk)
}
