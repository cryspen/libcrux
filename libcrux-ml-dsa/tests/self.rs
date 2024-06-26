use rand::{rngs::OsRng, RngCore};

fn random_array<const L: usize>() -> [u8; L] {
    let mut rng = OsRng;
    let mut seed = [0; L];
    rng.try_fill_bytes(&mut seed).unwrap();
    seed
}

macro_rules! impl_consistency {
    ($name:ident, $key_gen:expr, $sign:expr, $verify:expr) => {
        #[test]
        fn $name() {
            let key_generation_seed = random_array();
            let signing_randomness = random_array();

            // TODO: Choose the length randomly
            let message = random_array::<94883>();

            let key_pair = $key_gen(key_generation_seed);

            let signature = $sign(key_pair.signing_key, &message, signing_randomness);

            $verify(key_pair.verification_key, &message, signature)
                .expect("Verification should pass since the signature was honestly generated");
        }
    };
}

impl_consistency!(
    consistency_44,
    libcrux_ml_dsa::ml_dsa_44::generate_key_pair,
    libcrux_ml_dsa::ml_dsa_44::sign,
    libcrux_ml_dsa::ml_dsa_44::verify
);

impl_consistency!(
    consistency_65,
    libcrux_ml_dsa::ml_dsa_65::generate_key_pair,
    libcrux_ml_dsa::ml_dsa_65::sign,
    libcrux_ml_dsa::ml_dsa_65::verify
);

impl_consistency!(
    consistency_87,
    libcrux_ml_dsa::ml_dsa_87::generate_key_pair,
    libcrux_ml_dsa::ml_dsa_87::sign,
    libcrux_ml_dsa::ml_dsa_87::verify
);
