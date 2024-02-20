use libcrux::{
    digest::incremental::{AbsorbManySqueezeOnceShake128, AbsorbOnceSqueezeManyShake128},
    kem,
};

struct Shake128Rng {
    buffer: Vec<u8>,
    shake128: AbsorbOnceSqueezeManyShake128,
}

impl Shake128Rng {
    // The number of bytes needed per round when the parameter set is:
    //
    // - Kyber512 = 64 + 32 + 768 = 864
    // - Kyber768 =  64 + 32 + 1088 = 1184
    // - Kyber1024 = 64 + 32 + 1568 = 1664
    //
    // The SHAKE128 block size is 168 bytes.
    //
    // TODO: We can clean up this Rng using the above facts, but to keep things
    // simple for now we set:
    // |BUFFER_SIZE| = 168,000
    const BUFFER_SIZE: u32 = 168_000;

    pub fn new() -> Self {
        let mut shake128 = AbsorbOnceSqueezeManyShake128::new();
        shake128.absorb(&[]);

        let buffer = shake128
            .squeeze_nblocks::<{ Self::BUFFER_SIZE as usize }>()
            .to_vec();

        Self { buffer, shake128 }
    }

    pub fn read<const OUTPUT_BYTES: usize>(&mut self) -> [u8; OUTPUT_BYTES] {
        if self.buffer.len() < OUTPUT_BYTES {
            self.buffer.extend_from_slice(
                &self
                    .shake128
                    .squeeze_nblocks::<{ Self::BUFFER_SIZE as usize }>(),
            );
        }

        self.buffer
            .drain(0..OUTPUT_BYTES)
            .collect::<Vec<_>>()
            .as_slice()
            .try_into()
            .unwrap()
    }
}

macro_rules! impl_shake128_rng_answer_tests {
    ($name:ident, $kat_rounds:literal, $ciphertext_size:literal, $key_gen_derand:expr, $encapsulate_derand:expr, $decapsulate_derand: expr, $expected_final_hash:expr) => {
        #[test]
        fn $name() {
            let mut rng = Shake128Rng::new();
            let mut shake128 = AbsorbManySqueezeOnceShake128::new();

            for _ in 0..$kat_rounds {
                let key_generation_seed = rng.read::<64>();
                let key_pair = $key_gen_derand(key_generation_seed);

                // TODO: See if there's a way to parallelize this, perhaps
                // using a different hash function?
                shake128.absorb(key_pair.public_key().as_ref());
                shake128.absorb(key_pair.private_key().as_ref());

                let encapsulation_seed = rng.read::<32>();
                let (ciphertext, shared_secret) =
                    $encapsulate_derand(key_pair.public_key(), encapsulation_seed);

                let decapsulated_shared_secret =
                    $decapsulate_derand(key_pair.private_key(), &ciphertext);
                assert_eq!(decapsulated_shared_secret, shared_secret);

                shake128.absorb(ciphertext.as_ref());
                shake128.absorb(shared_secret.as_ref());

                let invalid_ciphertext = rng.read::<$ciphertext_size>();
                let implicit_rejection_secret =
                    $decapsulate_derand(key_pair.private_key(), &invalid_ciphertext.into());

                shake128.absorb(implicit_rejection_secret.as_ref());
            }

            let final_hash: [u8; 32] = shake128.squeeze::<32>();
            assert_eq!(hex::encode(&final_hash), $expected_final_hash);
        }
    };
}

// The 5,000 KAT tests.

impl_shake128_rng_answer_tests!(
    kyber512_shake128_rng_5000_known_answer_tests,
    5000,
    768,
    kem::deterministic::kyber512_generate_keypair_derand,
    kem::deterministic::kyber512_encapsulate_derand,
    kem::deterministic::kyber512_decapsulate_derand,
    "e837d3b8ede8fe19a2442d25c921851811f87d054b66e453b82b620582ab0629"
);
impl_shake128_rng_answer_tests!(
    kyber768_shake128_rng_5000_known_answer_tests,
    5000,
    1088,
    kem::deterministic::kyber768_generate_keypair_derand,
    kem::deterministic::kyber768_encapsulate_derand,
    kem::deterministic::kyber768_decapsulate_derand,
    "17745bc1564b01ab4752e86438973d7120e92d46082c33d05dbef07f0688cc77"
);
impl_shake128_rng_answer_tests!(
    kyber1024_shake128_rng_5000_known_answer_tests,
    5000,
    1568,
    kem::deterministic::kyber1024_generate_keypair_derand,
    kem::deterministic::kyber1024_encapsulate_derand,
    kem::deterministic::kyber1024_decapsulate_derand,
    "44079dcea6b7d596c0c00431f012e0f3b63777736720921fdc50668d9c0c6ad0"
);

// The 100,000 KAT tests.

#[cfg(feature = "slow_kat_tests")]
impl_shake128_rng_answer_tests!(
    kyber512_shake128_rng_100_000_known_answer_tests,
    100_000,
    768,
    kem::deterministic::kyber512_generate_keypair_derand,
    kem::deterministic::kyber512_encapsulate_derand,
    kem::deterministic::kyber512_decapsulate_derand,
    "99520ba1dd26f7da7d5c8e71110cb12b6c15664478b0ea0dbb7991c74e374392"
);

#[cfg(feature = "slow_kat_tests")]
impl_shake128_rng_answer_tests!(
    kyber768_shake128_rng_100_000_known_answer_tests,
    100_000,
    1088,
    kem::deterministic::kyber768_generate_keypair_derand,
    kem::deterministic::kyber768_encapsulate_derand,
    kem::deterministic::kyber768_decapsulate_derand,
    "35d56f1cc040b71fc97a9b77b05485d97354b296483d2539ade224374ec8d325"
);

#[cfg(feature = "slow_kat_tests")]
impl_shake128_rng_answer_tests!(
    kyber1024_shake128_rng_100_000_known_answer_tests,
    100_000,
    1568,
    kem::deterministic::kyber1024_generate_keypair_derand,
    kem::deterministic::kyber1024_encapsulate_derand,
    kem::deterministic::kyber1024_decapsulate_derand,
    "b9440d4fe3231bf70cb07f6f7ebd6ffaa469b3f08e644a1449e851f30e4d0d23"
);
