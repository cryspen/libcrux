#![no_main]
use libfuzzer_sys::fuzz_target;

use libcrux::{
    digest::shake256,
    kem::{self, Algorithm, Ct, PrivateKey},
};
use rand::{CryptoRng, Rng, RngCore};

struct FuzzRng {
    data: Vec<u8>,
}

impl RngCore for FuzzRng {
    fn next_u32(&mut self) -> u32 {
        let mut bytes: [u8; 4] = [0; 4];
        self.fill_bytes(&mut bytes);
        u32::from_be_bytes(bytes)
    }

    fn next_u64(&mut self) -> u64 {
        todo!()
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        dest.copy_from_slice(&self.data[0..dest.len()]);
        self.data = self.data.drain(dest.len()..).collect();
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand::Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}

impl CryptoRng for FuzzRng {}

fn modify_ciphertext(alg: Algorithm, rng: &mut (impl CryptoRng + Rng), ciphertext: Ct) -> Ct {
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

const SHARED_SECRET_SIZE: usize = 32;

fn modify_secret_key(
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

fn compute_implicit_rejection_shared_secret(
    ciphertext: Ct,
    secret_key: PrivateKey,
) -> [u8; SHARED_SECRET_SIZE] {
    let raw_secret_key = secret_key.encode();

    let mut to_hash = raw_secret_key[raw_secret_key.len() - SHARED_SECRET_SIZE..].to_vec();
    to_hash.extend_from_slice(&ciphertext.encode());

    shake256(&to_hash)
}

fuzz_target!(|data: &[u8]| {
    if data.len() < 256 {
        // This is not enough randomness for the test.
        return;
    }

    let mut rng = FuzzRng {
        data: data.to_vec(),
    };

    if let Ok((secret_key, public_key)) = kem::key_gen(Algorithm::Kyber768, &mut rng) {
        if let Ok((_, ciphertext)) = kem::encapsulate(&public_key, &mut rng) {
            let ciphertext = modify_ciphertext(Algorithm::Kyber768, &mut rng, ciphertext);
            let shared_secret_decapsulated = kem::decapsulate(&ciphertext, &secret_key).unwrap();

            let secret_key = modify_secret_key(Algorithm::Kyber768, &mut rng, secret_key, true);
            let shared_secret_decapsulated_1 = kem::decapsulate(&ciphertext, &secret_key).unwrap();

            assert_ne!(
                shared_secret_decapsulated.encode(),
                shared_secret_decapsulated_1.encode()
            );

            assert_eq!(
                shared_secret_decapsulated_1.encode(),
                compute_implicit_rejection_shared_secret(ciphertext, secret_key)
            );
        }
    }
});
