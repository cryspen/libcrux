use libcrux_ml_kem::{mlkem1024, mlkem512, mlkem768, MlKemCiphertext, MlKemPrivateKey};
use libcrux_sha3::shake256;
use rand::{rngs::OsRng, thread_rng, RngCore};

const SHARED_SECRET_SIZE: usize = 32;

fn random_array<const L: usize>() -> [u8; L] {
    let mut rng = OsRng;
    let mut seed = [0; L];
    rng.try_fill_bytes(&mut seed).unwrap();
    seed
}

macro_rules! impl_consistency {
    ($name:ident, $key_gen:expr, $encaps:expr, $decaps:expr) => {
        #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
        #[test]
        fn $name() {
            let randomness = random_array();
            let key_pair = $key_gen(randomness);
            let randomness = random_array();
            let (ciphertext, shared_secret) = $encaps(key_pair.public_key(), randomness);
            let shared_secret_decapsulated = $decaps(key_pair.private_key(), &ciphertext);
            assert_eq!(
                shared_secret, shared_secret_decapsulated,
                "lhs: shared_secret, rhs: shared_secret_decapsulated"
            );

            // If the randomness was not enough for the rejection sampling step
            // in key-generation and encapsulation, simply return without
            // failing.
        }
    };
}

fn modify_ciphertext<const LEN: usize>(
    mut ciphertext: MlKemCiphertext<LEN>,
) -> MlKemCiphertext<LEN> {
    let mut random_u32: usize = thread_rng().next_u32().try_into().unwrap();

    let mut random_byte: u8 = (random_u32 & 0xFF) as u8;
    if random_byte == 0 {
        random_byte += 1;
    }
    random_u32 >>= 8;

    let position = random_u32 % ciphertext.len();
    ciphertext[position] ^= random_byte;

    ciphertext
}

macro_rules! impl_modified_ciphertext {
    ($name:ident, $key_gen:expr, $encaps:expr, $decaps:expr) => {
        #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
        #[test]
        fn $name() {
            let randomness = random_array();
            let key_pair = $key_gen(randomness);
            let randomness = random_array();
            let (ciphertext, shared_secret) = $encaps(key_pair.public_key(), randomness);

            let ciphertext = modify_ciphertext(ciphertext);
            let shared_secret_decapsulated = $decaps(key_pair.private_key(), &ciphertext);

            assert_ne!(shared_secret, shared_secret_decapsulated);

            // if the randomness was not enough for the rejection sampling step
            // in key-generation and encapsulation, simply return without
            // failing.
        }
    };
}

fn modify_secret_key<const LEN: usize>(
    secret_key: &MlKemPrivateKey<LEN>,
    modify_implicit_rejection_value: bool,
) -> MlKemPrivateKey<LEN> {
    let mut raw_secret_key: MlKemPrivateKey<LEN> = secret_key.as_slice().into();

    let mut random_u32: usize = thread_rng().next_u32().try_into().unwrap();

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

    raw_secret_key
}

fn compute_implicit_rejection_shared_secret<const CLEN: usize, const LEN: usize>(
    ciphertext: MlKemCiphertext<CLEN>,
    secret_key: MlKemPrivateKey<LEN>,
) -> [u8; SHARED_SECRET_SIZE] {
    let mut to_hash = secret_key[secret_key.len() - SHARED_SECRET_SIZE..].to_vec();
    to_hash.extend_from_slice(ciphertext.as_ref());

    shake256(&to_hash)
}

macro_rules! impl_modified_secret_key {
    ($name:ident, $key_gen:expr, $encaps:expr, $decaps:expr) => {
        #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
        #[test]
        fn $name() {
            let randomness = random_array();
            let key_pair = $key_gen(randomness);
            let randomness = random_array();
            let (ciphertext, _) = $encaps(key_pair.public_key(), randomness);

            let secret_key = modify_secret_key(key_pair.private_key(), false);
            let shared_secret_decapsulated = $decaps(&secret_key, &ciphertext);

            assert_eq!(
                shared_secret_decapsulated,
                compute_implicit_rejection_shared_secret(ciphertext, secret_key)
            );

            // if the randomness was not enough for the rejection sampling step
            // in key-generation and encapsulation, simply return without
            // failing.
        }
    };
}

macro_rules! impl_modified_ciphertext_and_implicit_rejection_value {
    ($name:ident, $key_gen:expr, $encaps:expr, $decaps:expr) => {
        #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
        #[test]
        fn $name() {
            let randomness = random_array();
            let key_pair = $key_gen(randomness);
            let randomness = random_array();
            let (ciphertext, _) = $encaps(key_pair.public_key(), randomness);

            let ciphertext = modify_ciphertext(ciphertext);
            let shared_secret_decapsulated = $decaps(key_pair.private_key(), &ciphertext);

            let secret_key = modify_secret_key(key_pair.private_key(), true);
            let shared_secret_decapsulated_ms = $decaps(&secret_key, &ciphertext);

            assert_ne!(shared_secret_decapsulated, shared_secret_decapsulated_ms);

            assert_eq!(
                shared_secret_decapsulated_ms,
                compute_implicit_rejection_shared_secret(ciphertext, secret_key)
            );

            // if the randomness was not enough for the rejection sampling step
            // in key-generation and encapsulation, simply return without
            // failing.
        }
    };
}

impl_consistency!(
    consistency_512,
    mlkem512::generate_key_pair,
    mlkem512::encapsulate,
    mlkem512::decapsulate
);
impl_consistency!(
    consistency_768,
    mlkem768::generate_key_pair,
    mlkem768::encapsulate,
    mlkem768::decapsulate
);
impl_consistency!(
    consistency_1024,
    mlkem1024::generate_key_pair,
    mlkem1024::encapsulate,
    mlkem1024::decapsulate
);

impl_modified_ciphertext!(
    modified_ciphertext_512,
    mlkem1024::generate_key_pair,
    mlkem1024::encapsulate,
    mlkem1024::decapsulate
);
impl_modified_ciphertext!(
    modified_ciphertext_768,
    mlkem1024::generate_key_pair,
    mlkem1024::encapsulate,
    mlkem1024::decapsulate
);
impl_modified_ciphertext!(
    modified_ciphertext_1024,
    mlkem1024::generate_key_pair,
    mlkem1024::encapsulate,
    mlkem1024::decapsulate
);

impl_modified_secret_key!(
    modified_secret_key_512,
    mlkem1024::generate_key_pair,
    mlkem1024::encapsulate,
    mlkem1024::decapsulate
);
impl_modified_secret_key!(
    modified_secret_key_768,
    mlkem1024::generate_key_pair,
    mlkem1024::encapsulate,
    mlkem1024::decapsulate
);
impl_modified_secret_key!(
    modified_secret_key_1024,
    mlkem1024::generate_key_pair,
    mlkem1024::encapsulate,
    mlkem1024::decapsulate
);

impl_modified_ciphertext_and_implicit_rejection_value!(
    modified_ciphertext_and_implicit_rejection_value_512,
    mlkem1024::generate_key_pair,
    mlkem1024::encapsulate,
    mlkem1024::decapsulate
);
impl_modified_ciphertext_and_implicit_rejection_value!(
    modified_ciphertext_and_implicit_rejection_value_768,
    mlkem1024::generate_key_pair,
    mlkem1024::encapsulate,
    mlkem1024::decapsulate
);
impl_modified_ciphertext_and_implicit_rejection_value!(
    modified_ciphertext_and_implicit_rejection_value_1024,
    mlkem1024::generate_key_pair,
    mlkem1024::encapsulate,
    mlkem1024::decapsulate
);
