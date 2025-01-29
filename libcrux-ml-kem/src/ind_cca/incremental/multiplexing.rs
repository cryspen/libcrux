use super::*;

#[cfg(feature = "simd256")]
use avx2::{
    as_keypair as as_avx2_keypair, as_state as as_avx2_state, decapsulate as decapsulate_avx2,
    decapsulate_incremental_key as decapsulate_incremental_key_avx2,
    encapsulate1 as encapsulate1_avx2, encapsulate1_serialized as encapsulate1_serialized_avx2,
    encapsulate2 as encapsulate2_avx2, encapsulate2_serialized as encapsulate2_serialized_avx2,
    generate_keypair as generate_keypair_avx2,
    generate_keypair_serialized as generate_keypair_serialized_avx2,
    validate_pk as validate_pk_avx2,
};

#[cfg(feature = "simd128")]
use neon::{
    as_keypair as as_neon_keypair, as_state as as_neon_state, decapsulate as decapsulate_neon,
    decapsulate_incremental_key as decapsulate_incremental_key_neon,
    encapsulate1 as encapsulate1_neon, encapsulate1_serialized as encapsulate1_serialized_neon,
    encapsulate2 as encapsulate2_neon, encapsulate2_serialized as encapsulate2_serialized_neon,
    generate_keypair as generate_keypair_neon,
    generate_keypair_serialized as generate_keypair_serialized_neon,
    validate_pk as validate_pk_neon,
};

#[cfg(not(feature = "simd256"))]
use portable::{
    as_keypair as as_avx2_keypair, as_state as as_avx2_state, decapsulate as decapsulate_avx2,
    decapsulate_incremental_key as decapsulate_incremental_key_avx2,
    encapsulate1 as encapsulate1_avx2, encapsulate1_serialized as encapsulate1_serialized_avx2,
    encapsulate2 as encapsulate2_avx2, encapsulate2_serialized as encapsulate2_serialized_avx2,
    generate_keypair as generate_keypair_avx2,
    generate_keypair_serialized as generate_keypair_serialized_avx2,
    validate_pk as validate_pk_avx2,
};

#[cfg(not(feature = "simd128"))]
use portable::{
    as_keypair as as_neon_keypair, as_state as as_neon_state, decapsulate as decapsulate_neon,
    decapsulate_incremental_key as decapsulate_incremental_key_neon,
    encapsulate1 as encapsulate1_neon, encapsulate1_serialized as encapsulate1_serialized_neon,
    encapsulate2 as encapsulate2_neon, encapsulate2_serialized as encapsulate2_serialized_neon,
    generate_keypair as generate_keypair_neon,
    generate_keypair_serialized as generate_keypair_serialized_neon,
    validate_pk as validate_pk_neon,
};

/// Functions in this module require an allocator to use [`Box`].
///
/// Instead of serializing keys and state, the functions in this module return
/// the platform dependent keys and state types for immediate use.
#[cfg(feature = "alloc")]
pub(crate) mod alloc {
    use super::*;

    use ::alloc::boxed::Box;

    pub(crate) fn generate_keypair<
        const K: usize,
        const CPA_PRIVATE_KEY_SIZE: usize,
        const PRIVATE_KEY_SIZE: usize,
        const PUBLIC_KEY_SIZE: usize,
        const BYTES_PER_RING_ELEMENT: usize,
        const ETA1: usize,
        const ETA1_RANDOMNESS_SIZE: usize,
    >(
        randomness: [u8; KEY_GENERATION_SEED_SIZE],
    ) -> Box<dyn Keys> {
        if libcrux_platform::simd256_support() {
            Box::new(generate_keypair_avx2::<
                K,
                CPA_PRIVATE_KEY_SIZE,
                PRIVATE_KEY_SIZE,
                PUBLIC_KEY_SIZE,
                BYTES_PER_RING_ELEMENT,
                ETA1,
                ETA1_RANDOMNESS_SIZE,
            >(randomness))
        } else if libcrux_platform::simd128_support() {
            Box::new(generate_keypair_neon::<
                K,
                CPA_PRIVATE_KEY_SIZE,
                PRIVATE_KEY_SIZE,
                PUBLIC_KEY_SIZE,
                BYTES_PER_RING_ELEMENT,
                ETA1,
                ETA1_RANDOMNESS_SIZE,
            >(randomness))
        } else {
            Box::new(portable::generate_keypair::<
                K,
                CPA_PRIVATE_KEY_SIZE,
                PRIVATE_KEY_SIZE,
                PUBLIC_KEY_SIZE,
                BYTES_PER_RING_ELEMENT,
                ETA1,
                ETA1_RANDOMNESS_SIZE,
            >(randomness))
        }
    }

    pub(crate) fn encapsulate1<
        const K: usize,
        const CIPHERTEXT_SIZE: usize,
        const C1_SIZE: usize,
        const VECTOR_U_COMPRESSION_FACTOR: usize,
        const VECTOR_U_BLOCK_LEN: usize,
        const ETA1: usize,
        const ETA1_RANDOMNESS_SIZE: usize,
        const ETA2: usize,
        const ETA2_RANDOMNESS_SIZE: usize,
    >(
        public_key_part: &PublicKey1,
        randomness: [u8; SHARED_SECRET_SIZE],
    ) -> (Ciphertext1<C1_SIZE>, Box<dyn State>) {
        if libcrux_platform::simd256_support() {
            let (c, s) = encapsulate1_avx2::<
                K,
                CIPHERTEXT_SIZE,
                C1_SIZE,
                VECTOR_U_COMPRESSION_FACTOR,
                VECTOR_U_BLOCK_LEN,
                ETA1,
                ETA1_RANDOMNESS_SIZE,
                ETA2,
                ETA2_RANDOMNESS_SIZE,
            >(public_key_part, randomness);
            (c, Box::new(s))
        } else if libcrux_platform::simd128_support() {
            let (c, s) = encapsulate1_neon::<
                K,
                CIPHERTEXT_SIZE,
                C1_SIZE,
                VECTOR_U_COMPRESSION_FACTOR,
                VECTOR_U_BLOCK_LEN,
                ETA1,
                ETA1_RANDOMNESS_SIZE,
                ETA2,
                ETA2_RANDOMNESS_SIZE,
            >(public_key_part, randomness);
            (c, Box::new(s))
        } else {
            let (c, s) = portable::encapsulate1::<
                K,
                CIPHERTEXT_SIZE,
                C1_SIZE,
                VECTOR_U_COMPRESSION_FACTOR,
                VECTOR_U_BLOCK_LEN,
                ETA1,
                ETA1_RANDOMNESS_SIZE,
                ETA2,
                ETA2_RANDOMNESS_SIZE,
            >(public_key_part, randomness);
            (c, Box::new(s))
        }
    }

    pub(crate) fn encapsulate2<
        const K: usize,
        const PK2_LEN: usize,
        const C2_SIZE: usize,
        const VECTOR_V_COMPRESSION_FACTOR: usize,
    >(
        state: &dyn State,
        public_key_part: &[u8],
    ) -> Result<Ciphertext2<C2_SIZE>, Error> {
        if libcrux_platform::simd256_support() {
            let state = as_avx2_state(state.as_any());
            let pk2 = PublicKey2::try_from(public_key_part)?;
            Ok(encapsulate2_avx2::<
                K,
                PK2_LEN,
                C2_SIZE,
                VECTOR_V_COMPRESSION_FACTOR,
            >(state, &pk2))
        } else if libcrux_platform::simd128_support() {
            let state = as_neon_state(state.as_any());
            let pk2 = PublicKey2::try_from(public_key_part)?;
            Ok(encapsulate2_neon::<
                K,
                PK2_LEN,
                C2_SIZE,
                VECTOR_V_COMPRESSION_FACTOR,
            >(state, &pk2))
        } else {
            let state = portable::as_state(state.as_any());
            let pk2 = PublicKey2::try_from(public_key_part)?;
            Ok(portable::encapsulate2::<
                K,
                PK2_LEN,
                C2_SIZE,
                VECTOR_V_COMPRESSION_FACTOR,
            >(state, &pk2))
        }
    }

    pub(crate) fn decapsulate<
        const K: usize,
        const SECRET_KEY_SIZE: usize,
        const CPA_SECRET_KEY_SIZE: usize,
        const PUBLIC_KEY_SIZE: usize,
        const CIPHERTEXT_SIZE: usize,
        const T_AS_NTT_ENCODED_SIZE: usize,
        const C1_SIZE: usize,
        const C2_SIZE: usize,
        const VECTOR_U_COMPRESSION_FACTOR: usize,
        const VECTOR_V_COMPRESSION_FACTOR: usize,
        const C1_BLOCK_SIZE: usize,
        const ETA1: usize,
        const ETA1_RANDOMNESS_SIZE: usize,
        const ETA2: usize,
        const ETA2_RANDOMNESS_SIZE: usize,
        const IMPLICIT_REJECTION_HASH_INPUT_SIZE: usize,
    >(
        private_key: &dyn Keys,
        ciphertext1: &Ciphertext1<C1_SIZE>,
        ciphertext2: &Ciphertext2<C2_SIZE>,
    ) -> MlKemSharedSecret {
        if libcrux_platform::simd256_support() {
            let private_key = as_avx2_keypair(private_key.as_any());
            decapsulate_avx2::<
                K,
                SECRET_KEY_SIZE,
                CPA_SECRET_KEY_SIZE,
                PUBLIC_KEY_SIZE,
                CIPHERTEXT_SIZE,
                T_AS_NTT_ENCODED_SIZE,
                C1_SIZE,
                C2_SIZE,
                VECTOR_U_COMPRESSION_FACTOR,
                VECTOR_V_COMPRESSION_FACTOR,
                C1_BLOCK_SIZE,
                ETA1,
                ETA1_RANDOMNESS_SIZE,
                ETA2,
                ETA2_RANDOMNESS_SIZE,
                IMPLICIT_REJECTION_HASH_INPUT_SIZE,
            >(private_key, ciphertext1, ciphertext2)
        } else if libcrux_platform::simd128_support() {
            let private_key = as_neon_keypair(private_key.as_any());
            decapsulate_neon::<
                K,
                SECRET_KEY_SIZE,
                CPA_SECRET_KEY_SIZE,
                PUBLIC_KEY_SIZE,
                CIPHERTEXT_SIZE,
                T_AS_NTT_ENCODED_SIZE,
                C1_SIZE,
                C2_SIZE,
                VECTOR_U_COMPRESSION_FACTOR,
                VECTOR_V_COMPRESSION_FACTOR,
                C1_BLOCK_SIZE,
                ETA1,
                ETA1_RANDOMNESS_SIZE,
                ETA2,
                ETA2_RANDOMNESS_SIZE,
                IMPLICIT_REJECTION_HASH_INPUT_SIZE,
            >(private_key, ciphertext1, ciphertext2)
        } else {
            let private_key = portable::as_keypair(private_key.as_any());
            portable::decapsulate::<
                K,
                SECRET_KEY_SIZE,
                CPA_SECRET_KEY_SIZE,
                PUBLIC_KEY_SIZE,
                CIPHERTEXT_SIZE,
                T_AS_NTT_ENCODED_SIZE,
                C1_SIZE,
                C2_SIZE,
                VECTOR_U_COMPRESSION_FACTOR,
                VECTOR_V_COMPRESSION_FACTOR,
                C1_BLOCK_SIZE,
                ETA1,
                ETA1_RANDOMNESS_SIZE,
                ETA2,
                ETA2_RANDOMNESS_SIZE,
                IMPLICIT_REJECTION_HASH_INPUT_SIZE,
            >(private_key, ciphertext1, ciphertext2)
        }
    }
}

pub(crate) fn generate_keypair<
    const K: usize,
    const PK2_LEN: usize,
    const CPA_PRIVATE_KEY_SIZE: usize,
    const PRIVATE_KEY_SIZE: usize,
    const PUBLIC_KEY_SIZE: usize,
    const BYTES_PER_RING_ELEMENT: usize,
    const ETA1: usize,
    const ETA1_RANDOMNESS_SIZE: usize,
>(
    randomness: [u8; KEY_GENERATION_SEED_SIZE],
    key_pair: &mut [u8],
) -> Result<(), Error> {
    if libcrux_platform::simd256_support() {
        generate_keypair_serialized_avx2::<
            K,
            PK2_LEN,
            CPA_PRIVATE_KEY_SIZE,
            PRIVATE_KEY_SIZE,
            PUBLIC_KEY_SIZE,
            BYTES_PER_RING_ELEMENT,
            ETA1,
            ETA1_RANDOMNESS_SIZE,
        >(randomness, key_pair)
    } else if libcrux_platform::simd128_support() {
        generate_keypair_serialized_neon::<
            K,
            PK2_LEN,
            CPA_PRIVATE_KEY_SIZE,
            PRIVATE_KEY_SIZE,
            PUBLIC_KEY_SIZE,
            BYTES_PER_RING_ELEMENT,
            ETA1,
            ETA1_RANDOMNESS_SIZE,
        >(randomness, key_pair)
    } else {
        portable::generate_keypair_serialized::<
            K,
            PK2_LEN,
            CPA_PRIVATE_KEY_SIZE,
            PRIVATE_KEY_SIZE,
            PUBLIC_KEY_SIZE,
            BYTES_PER_RING_ELEMENT,
            ETA1,
            ETA1_RANDOMNESS_SIZE,
        >(randomness, key_pair)
    }
}

pub(crate) fn validate_pk<const K: usize, const PK_LEN: usize>(
    pk1: &PublicKey1,
    pk2: &[u8],
) -> Result<(), Error> {
    if libcrux_platform::simd256_support() {
        validate_pk_avx2::<K, PK_LEN>(pk1, pk2)
    } else if libcrux_platform::simd128_support() {
        validate_pk_neon::<K, PK_LEN>(pk1, pk2)
    } else {
        portable::validate_pk::<K, PK_LEN>(pk1, pk2)
    }
}

pub(crate) fn encapsulate1<
    const K: usize,
    const CIPHERTEXT_SIZE: usize,
    const C1_SIZE: usize,
    const VECTOR_U_COMPRESSION_FACTOR: usize,
    const VECTOR_U_BLOCK_LEN: usize,
    const ETA1: usize,
    const ETA1_RANDOMNESS_SIZE: usize,
    const ETA2: usize,
    const ETA2_RANDOMNESS_SIZE: usize,
>(
    public_key_part: &PublicKey1,
    randomness: [u8; SHARED_SECRET_SIZE],
    state: &mut [u8],
) -> Result<Ciphertext1<C1_SIZE>, Error> {
    if libcrux_platform::simd256_support() {
        encapsulate1_serialized_avx2::<
            K,
            CIPHERTEXT_SIZE,
            C1_SIZE,
            VECTOR_U_COMPRESSION_FACTOR,
            VECTOR_U_BLOCK_LEN,
            ETA1,
            ETA1_RANDOMNESS_SIZE,
            ETA2,
            ETA2_RANDOMNESS_SIZE,
        >(public_key_part, randomness, state)
    } else if libcrux_platform::simd128_support() {
        encapsulate1_serialized_neon::<
            K,
            CIPHERTEXT_SIZE,
            C1_SIZE,
            VECTOR_U_COMPRESSION_FACTOR,
            VECTOR_U_BLOCK_LEN,
            ETA1,
            ETA1_RANDOMNESS_SIZE,
            ETA2,
            ETA2_RANDOMNESS_SIZE,
        >(public_key_part, randomness, state)
    } else {
        portable::encapsulate1_serialized::<
            K,
            CIPHERTEXT_SIZE,
            C1_SIZE,
            VECTOR_U_COMPRESSION_FACTOR,
            VECTOR_U_BLOCK_LEN,
            ETA1,
            ETA1_RANDOMNESS_SIZE,
            ETA2,
            ETA2_RANDOMNESS_SIZE,
        >(public_key_part, randomness, state)
    }
}

pub(crate) fn encapsulate2<
    const K: usize,
    const PK2_LEN: usize,
    const C2_SIZE: usize,
    const VECTOR_V_COMPRESSION_FACTOR: usize,
>(
    state: &[u8],
    public_key_part: &[u8],
) -> Result<Ciphertext2<C2_SIZE>, Error> {
    if libcrux_platform::simd256_support() {
        let pk2 = PublicKey2::try_from(public_key_part)?;
        encapsulate2_serialized_avx2::<K, PK2_LEN, C2_SIZE, VECTOR_V_COMPRESSION_FACTOR>(
            state, &pk2,
        )
    } else if libcrux_platform::simd128_support() {
        let pk2 = PublicKey2::try_from(public_key_part)?;
        encapsulate2_serialized_neon::<K, PK2_LEN, C2_SIZE, VECTOR_V_COMPRESSION_FACTOR>(
            state, &pk2,
        )
    } else {
        let pk2 = PublicKey2::try_from(public_key_part)?;
        portable::encapsulate2_serialized::<K, PK2_LEN, C2_SIZE, VECTOR_V_COMPRESSION_FACTOR>(
            state, &pk2,
        )
    }
}

pub(crate) fn decapsulate<
    const K: usize,
    const PK2_LEN: usize,
    const SECRET_KEY_SIZE: usize,
    const CPA_SECRET_KEY_SIZE: usize,
    const PUBLIC_KEY_SIZE: usize,
    const CIPHERTEXT_SIZE: usize,
    const T_AS_NTT_ENCODED_SIZE: usize,
    const C1_SIZE: usize,
    const C2_SIZE: usize,
    const VECTOR_U_COMPRESSION_FACTOR: usize,
    const VECTOR_V_COMPRESSION_FACTOR: usize,
    const C1_BLOCK_SIZE: usize,
    const ETA1: usize,
    const ETA1_RANDOMNESS_SIZE: usize,
    const ETA2: usize,
    const ETA2_RANDOMNESS_SIZE: usize,
    const IMPLICIT_REJECTION_HASH_INPUT_SIZE: usize,
>(
    private_key: &[u8],
    ciphertext1: &Ciphertext1<C1_SIZE>,
    ciphertext2: &Ciphertext2<C2_SIZE>,
) -> Result<MlKemSharedSecret, Error> {
    if libcrux_platform::simd256_support() {
        decapsulate_incremental_key_avx2::<
            K,
            PK2_LEN,
            SECRET_KEY_SIZE,
            CPA_SECRET_KEY_SIZE,
            PUBLIC_KEY_SIZE,
            CIPHERTEXT_SIZE,
            T_AS_NTT_ENCODED_SIZE,
            C1_SIZE,
            C2_SIZE,
            VECTOR_U_COMPRESSION_FACTOR,
            VECTOR_V_COMPRESSION_FACTOR,
            C1_BLOCK_SIZE,
            ETA1,
            ETA1_RANDOMNESS_SIZE,
            ETA2,
            ETA2_RANDOMNESS_SIZE,
            IMPLICIT_REJECTION_HASH_INPUT_SIZE,
        >(private_key, ciphertext1, ciphertext2)
    } else if libcrux_platform::simd128_support() {
        decapsulate_incremental_key_neon::<
            K,
            PK2_LEN,
            SECRET_KEY_SIZE,
            CPA_SECRET_KEY_SIZE,
            PUBLIC_KEY_SIZE,
            CIPHERTEXT_SIZE,
            T_AS_NTT_ENCODED_SIZE,
            C1_SIZE,
            C2_SIZE,
            VECTOR_U_COMPRESSION_FACTOR,
            VECTOR_V_COMPRESSION_FACTOR,
            C1_BLOCK_SIZE,
            ETA1,
            ETA1_RANDOMNESS_SIZE,
            ETA2,
            ETA2_RANDOMNESS_SIZE,
            IMPLICIT_REJECTION_HASH_INPUT_SIZE,
        >(private_key, ciphertext1, ciphertext2)
    } else {
        portable::decapsulate_incremental_key::<
            K,
            PK2_LEN,
            SECRET_KEY_SIZE,
            CPA_SECRET_KEY_SIZE,
            PUBLIC_KEY_SIZE,
            CIPHERTEXT_SIZE,
            T_AS_NTT_ENCODED_SIZE,
            C1_SIZE,
            C2_SIZE,
            VECTOR_U_COMPRESSION_FACTOR,
            VECTOR_V_COMPRESSION_FACTOR,
            C1_BLOCK_SIZE,
            ETA1,
            ETA1_RANDOMNESS_SIZE,
            ETA2,
            ETA2_RANDOMNESS_SIZE,
            IMPLICIT_REJECTION_HASH_INPUT_SIZE,
        >(private_key, ciphertext1, ciphertext2)
    }
}
