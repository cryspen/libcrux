use libcrux::{
    digest::incremental::{AbsorbManySqueezeOnceShake128, AbsorbOnceSqueezeManyShake128},
    kem,
};

struct Shake128Rng {
    buffer: Vec<u8>,
    shake128: AbsorbOnceSqueezeManyShake128,
}

impl Shake128Rng {
    // Each round of KAT testing will request need 1184 bytes, the
    // SHAKE128 block size is 168 bytes. |BUFFER_SIZE| = lcm(1184, 168) * 10
    const BUFFER_SIZE: u32 = 248_640;

    pub fn new() -> Self {
        let mut shake128 = AbsorbOnceSqueezeManyShake128::new();
        shake128.absorb(&[]);

        let buffer = shake128
            .squeeze_nblocks::<{ Self::BUFFER_SIZE as usize }>()
            .to_vec();

        Self { buffer, shake128 }
    }

    pub fn read<const OUTPUT_BYTES: usize>(&mut self) -> [u8; OUTPUT_BYTES] {
        if self.buffer.is_empty() {
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

#[test]
fn kyber_768_100000_kats() {
    let mut rng = Shake128Rng::new();
    let mut shake128 = AbsorbManySqueezeOnceShake128::new();

    for _ in 0..100_000 {
        let key_generation_seed = rng.read::<64>();
        let key_pair = kem::kyber768_generate_keypair_derand(key_generation_seed);

        shake128.absorb(key_pair.public_key().as_ref());
        shake128.absorb(key_pair.private_key().as_ref());

        let encapsulation_seed = rng.read::<32>();
        let (ciphertext, shared_secret) =
            kem::kyber768_encapsulate_derand(key_pair.public_key(), encapsulation_seed);

        shake128.absorb(ciphertext.as_ref());
        shake128.absorb(shared_secret.as_ref());

        let invalid_ciphertext = rng.read::<1088>();
        let implicit_rejection_secret =
            kem::kyber768_decapsulate_derand(key_pair.private_key(), &invalid_ciphertext.into());

        shake128.absorb(implicit_rejection_secret.as_ref());
    }

    let all_kats_hash: [u8; 32] = shake128.squeeze::<32>();
    assert_eq!(
        hex::encode(&all_kats_hash),
        "35d56f1cc040b71fc97a9b77b05485d97354b296483d2539ade224374ec8d325"
    );
}
