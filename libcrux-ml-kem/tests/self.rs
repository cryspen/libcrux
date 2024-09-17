use libcrux_ml_kem::{MlKemCiphertext, MlKemPrivateKey};

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

#[cfg(all(feature = "pre-verification",))]
macro_rules! impl_consistency_unpacked {
    ($name:ident, $modp:path) => {
        #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
        #[test]
        fn $name() {
            use $modp as p;

            let randomness = random_array();

            // Generate unpacked key
            let mut key_pair_unpacked = Default::default();
            p::unpacked::generate_key_pair(randomness, &mut key_pair_unpacked);

            // Generate regular key
            let key_pair = p::generate_key_pair(randomness);

            // Ensure the two keys are the same
            let mut serialized_public_key = Default::default();
            p::unpacked::serialized_public_key(
                key_pair_unpacked.public_key(),
                &mut serialized_public_key,
            );
            assert_eq!(
                key_pair.public_key().as_slice(),
                serialized_public_key.as_slice()
            );
            let mut re_unpacked_public_key = Default::default();
            p::unpacked::unpacked_public_key(key_pair.public_key(), &mut re_unpacked_public_key);
            let mut serialized_public_key = Default::default();
            p::unpacked::serialized_public_key(&re_unpacked_public_key, &mut serialized_public_key);
            assert_eq!(
                serialized_public_key.as_slice(),
                key_pair.public_key().as_slice()
            );

            let randomness = random_array();
            let (ciphertext, shared_secret) = p::encapsulate(key_pair.public_key(), randomness);
            let (ciphertext_unpacked, shared_secret_unpacked) =
                p::unpacked::encapsulate(&key_pair_unpacked.public_key, randomness);
            assert_eq!(
                shared_secret, shared_secret_unpacked,
                "lhs: shared_secret, rhs: shared_secret_unpacked"
            );
            assert_eq!(
                ciphertext.as_slice(),
                ciphertext_unpacked.as_slice(),
                "lhs: ciphertext, rhs: ciphertext_unpacked"
            );
            let shared_secret_decapsulated =
                p::unpacked::decapsulate(&key_pair_unpacked, &ciphertext);
            let shared_secret = p::decapsulate(key_pair.private_key(), &ciphertext);
            assert_eq!(
                shared_secret_unpacked, shared_secret_decapsulated,
                "lhs: shared_secret_unpacked, rhs: shared_secret_decapsulated"
            );
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

fn modify_ciphertext<const LEN: usize>(ciphertext: MlKemCiphertext<LEN>) -> MlKemCiphertext<LEN> {
    let mut raw_ciphertext = [0u8; LEN];
    raw_ciphertext.copy_from_slice(ciphertext.as_ref());

    let mut random_u32: usize = thread_rng().next_u32().try_into().unwrap();

    let mut random_byte: u8 = (random_u32 & 0xFF) as u8;
    if random_byte == 0 {
        random_byte += 1;
    }
    random_u32 >>= 8;

    let position = random_u32 % MlKemCiphertext::<LEN>::len();
    raw_ciphertext[position] ^= random_byte;

    let ciphertext: [u8; LEN] = raw_ciphertext[0..MlKemCiphertext::<LEN>::len()]
        .try_into()
        .unwrap();

    ciphertext.into()
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
    let mut raw_secret_key = [0u8; LEN];
    raw_secret_key.copy_from_slice(secret_key.as_slice());

    let mut random_u32: usize = thread_rng().next_u32().try_into().unwrap();

    let mut random_byte: u8 = (random_u32 & 0xFF) as u8;
    if random_byte == 0 {
        random_byte += 1;
    }
    random_u32 >>= 8;

    let position = if modify_implicit_rejection_value {
        (MlKemPrivateKey::<LEN>::len() - SHARED_SECRET_SIZE) + (random_u32 % SHARED_SECRET_SIZE)
    } else {
        random_u32 % (MlKemPrivateKey::<LEN>::len() - SHARED_SECRET_SIZE)
    };

    raw_secret_key[position] ^= random_byte;

    let secret_key: [u8; LEN] = raw_secret_key[0..MlKemPrivateKey::<LEN>::len()]
        .try_into()
        .unwrap();

    secret_key.into()
}

fn compute_implicit_rejection_shared_secret<const CLEN: usize, const LEN: usize>(
    ciphertext: MlKemCiphertext<CLEN>,
    secret_key: MlKemPrivateKey<LEN>,
) -> [u8; SHARED_SECRET_SIZE] {
    let mut to_hash = secret_key[MlKemPrivateKey::<LEN>::len() - SHARED_SECRET_SIZE..].to_vec();
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

#[cfg(feature = "mlkem512")]
impl_consistency!(
    consistency_512,
    libcrux_ml_kem::mlkem512::generate_key_pair,
    libcrux_ml_kem::mlkem512::encapsulate,
    libcrux_ml_kem::mlkem512::decapsulate
);
#[cfg(feature = "mlkem768")]
impl_consistency!(
    consistency_768,
    libcrux_ml_kem::mlkem768::generate_key_pair,
    libcrux_ml_kem::mlkem768::encapsulate,
    libcrux_ml_kem::mlkem768::decapsulate
);
#[cfg(feature = "mlkem1024")]
impl_consistency!(
    consistency_1024,
    libcrux_ml_kem::mlkem1024::generate_key_pair,
    libcrux_ml_kem::mlkem1024::encapsulate,
    libcrux_ml_kem::mlkem1024::decapsulate
);

#[cfg(all(feature = "mlkem512", feature = "pre-verification",))]
impl_consistency_unpacked!(
    consistency_unpacked_512_portable,
    libcrux_ml_kem::mlkem512::portable
);

#[cfg(all(
    feature = "mlkem512",
    feature = "pre-verification",
    feature = "simd128",
))]
impl_consistency_unpacked!(
    consistency_unpacked_512_neon,
    libcrux_ml_kem::mlkem512::neon
);

#[cfg(all(
    feature = "mlkem512",
    feature = "pre-verification",
    feature = "simd256",
))]
impl_consistency_unpacked!(
    consistency_unpacked_512_avx2,
    libcrux_ml_kem::mlkem512::avx2
);

#[cfg(all(feature = "mlkem1024", feature = "pre-verification",))]
impl_consistency_unpacked!(
    consistency_unpacked_1024_portable,
    libcrux_ml_kem::mlkem1024::portable
);

#[cfg(all(
    feature = "mlkem1024",
    feature = "pre-verification",
    feature = "simd128",
))]
impl_consistency_unpacked!(
    consistency_unpacked_1024_neon,
    libcrux_ml_kem::mlkem1024::neon
);

#[cfg(all(
    feature = "mlkem1024",
    feature = "pre-verification",
    feature = "simd256",
))]
impl_consistency_unpacked!(
    consistency_unpacked_1024_avx2,
    libcrux_ml_kem::mlkem1024::avx2
);

#[cfg(all(feature = "mlkem768", feature = "pre-verification",))]
impl_consistency_unpacked!(
    consistency_unpacked_768_portable,
    libcrux_ml_kem::mlkem768::portable
);

#[cfg(all(
    feature = "mlkem768",
    feature = "pre-verification",
    feature = "simd128",
))]
impl_consistency_unpacked!(
    consistency_unpacked_768_neon,
    libcrux_ml_kem::mlkem768::neon
);

#[cfg(all(
    feature = "mlkem768",
    feature = "pre-verification",
    feature = "simd256",
))]
impl_consistency_unpacked!(
    consistency_unpacked_768_avx2,
    libcrux_ml_kem::mlkem768::avx2
);

#[cfg(feature = "mlkem512")]
impl_modified_ciphertext!(
    modified_ciphertext_512,
    libcrux_ml_kem::mlkem512::generate_key_pair,
    libcrux_ml_kem::mlkem512::encapsulate,
    libcrux_ml_kem::mlkem512::decapsulate
);
#[cfg(feature = "mlkem768")]
impl_modified_ciphertext!(
    modified_ciphertext_768,
    libcrux_ml_kem::mlkem768::generate_key_pair,
    libcrux_ml_kem::mlkem768::encapsulate,
    libcrux_ml_kem::mlkem768::decapsulate
);
#[cfg(feature = "mlkem1024")]
impl_modified_ciphertext!(
    modified_ciphertext_1024,
    libcrux_ml_kem::mlkem1024::generate_key_pair,
    libcrux_ml_kem::mlkem1024::encapsulate,
    libcrux_ml_kem::mlkem1024::decapsulate
);
#[cfg(feature = "mlkem512")]
impl_modified_secret_key!(
    modified_secret_key_512,
    libcrux_ml_kem::mlkem512::generate_key_pair,
    libcrux_ml_kem::mlkem512::encapsulate,
    libcrux_ml_kem::mlkem512::decapsulate
);
#[cfg(feature = "mlkem768")]
impl_modified_secret_key!(
    modified_secret_key_768,
    libcrux_ml_kem::mlkem768::generate_key_pair,
    libcrux_ml_kem::mlkem768::encapsulate,
    libcrux_ml_kem::mlkem768::decapsulate
);
#[cfg(feature = "mlkem1024")]
impl_modified_secret_key!(
    modified_secret_key_1024,
    libcrux_ml_kem::mlkem1024::generate_key_pair,
    libcrux_ml_kem::mlkem1024::encapsulate,
    libcrux_ml_kem::mlkem1024::decapsulate
);

#[cfg(feature = "mlkem512")]
impl_modified_ciphertext_and_implicit_rejection_value!(
    modified_ciphertext_and_implicit_rejection_value_512,
    libcrux_ml_kem::mlkem512::generate_key_pair,
    libcrux_ml_kem::mlkem512::encapsulate,
    libcrux_ml_kem::mlkem512::decapsulate
);
#[cfg(feature = "mlkem768")]
impl_modified_ciphertext_and_implicit_rejection_value!(
    modified_ciphertext_and_implicit_rejection_value_768,
    libcrux_ml_kem::mlkem768::generate_key_pair,
    libcrux_ml_kem::mlkem768::encapsulate,
    libcrux_ml_kem::mlkem768::decapsulate
);
#[cfg(feature = "mlkem1024")]
impl_modified_ciphertext_and_implicit_rejection_value!(
    modified_ciphertext_and_implicit_rejection_value_1024,
    libcrux_ml_kem::mlkem1024::generate_key_pair,
    libcrux_ml_kem::mlkem1024::encapsulate,
    libcrux_ml_kem::mlkem1024::decapsulate
);
