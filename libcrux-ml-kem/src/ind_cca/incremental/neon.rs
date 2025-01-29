use super::*;
type Vector = crate::vector::SIMD128Vector;
type Hash = crate::hash_functions::neon::Simd128Hash;

/// Downcast [`Keys`] to a neon [`MlKemKeyPairUnpacked`].
///
/// **PANICS** is the cast fails
pub(super) fn as_neon_keypair<const K: usize>(k: &dyn Any) -> &MlKemKeyPairUnpacked<K, Vector> {
    k.downcast_ref().unwrap()
}

/// Downcast [`State`] to a neon [`EncapsState`].
///
/// **PANICS** is the cast fails
pub(super) fn as_neon_state<const K: usize>(s: &dyn Any) -> &EncapsState<K, Vector> {
    s.downcast_ref().unwrap()
}

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
) -> MlKemKeyPairUnpacked<K, Vector> {
    super::generate_keypair::<
        K,
        CPA_PRIVATE_KEY_SIZE,
        PRIVATE_KEY_SIZE,
        PUBLIC_KEY_SIZE,
        BYTES_PER_RING_ELEMENT,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        Vector,
        Hash,
    >(randomness)
}

pub(crate) fn generate_keypair_serialized<
    const K: usize,
    const CPA_PRIVATE_KEY_SIZE: usize,
    const PRIVATE_KEY_SIZE: usize,
    const PUBLIC_KEY_SIZE: usize,
    const BYTES_PER_RING_ELEMENT: usize,
    const ETA1: usize,
    const ETA1_RANDOMNESS_SIZE: usize,
>(
    randomness: [u8; KEY_GENERATION_SEED_SIZE],
    key_pair: &mut [u8],
) {
    super::generate_keypair_serialized::<
        K,
        CPA_PRIVATE_KEY_SIZE,
        PRIVATE_KEY_SIZE,
        PUBLIC_KEY_SIZE,
        BYTES_PER_RING_ELEMENT,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        Vector,
        Hash,
    >(randomness, key_pair)
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
) -> (Ciphertext1<C1_SIZE>, EncapsState<K, Vector>) {
    super::encapsulate1::<
        K,
        CIPHERTEXT_SIZE,
        C1_SIZE,
        VECTOR_U_COMPRESSION_FACTOR,
        VECTOR_U_BLOCK_LEN,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        ETA2,
        ETA2_RANDOMNESS_SIZE,
        Vector,
        Hash,
    >(public_key_part, randomness)
}

pub(crate) fn encapsulate1_serialized<
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
    super::encapsulate1_serialized::<
        K,
        CIPHERTEXT_SIZE,
        C1_SIZE,
        VECTOR_U_COMPRESSION_FACTOR,
        VECTOR_U_BLOCK_LEN,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        ETA2,
        ETA2_RANDOMNESS_SIZE,
        Vector,
        Hash,
    >(public_key_part, randomness, state)
}

pub(crate) fn encapsulate2<
    const K: usize,
    const C2_SIZE: usize,
    const VECTOR_V_COMPRESSION_FACTOR: usize,
>(
    state: &EncapsState<K, Vector>,
    public_key_part: &PublicKey2<K, Vector>,
) -> Ciphertext2<C2_SIZE> {
    super::encapsulate2::<K, C2_SIZE, VECTOR_V_COMPRESSION_FACTOR, Vector>(state, public_key_part)
}

pub(crate) fn encapsulate2_serialized<
    const K: usize,
    const C2_SIZE: usize,
    const VECTOR_V_COMPRESSION_FACTOR: usize,
>(
    state: &[u8],
    public_key_part: &PublicKey2<K, Vector>,
) -> Result<Ciphertext2<C2_SIZE>, Error> {
    super::encapsulate2_serialized::<K, C2_SIZE, VECTOR_V_COMPRESSION_FACTOR, Vector>(
        state,
        public_key_part,
    )
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
    private_key: &MlKemKeyPairUnpacked<K, Vector>,
    ciphertext1: &Ciphertext1<C1_SIZE>,
    ciphertext2: &Ciphertext2<C2_SIZE>,
) -> MlKemSharedSecret {
    super::decapsulate::<
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
        Vector,
        Hash,
    >(private_key, ciphertext1, ciphertext2)
}

pub(crate) fn decapsulate_incremental_key<
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
    private_key: &[u8],
    ciphertext1: &Ciphertext1<C1_SIZE>,
    ciphertext2: &Ciphertext2<C2_SIZE>,
) -> Result<MlKemSharedSecret, Error> {
    super::decapsulate_incremental_key::<
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
        Vector,
        Hash,
    >(private_key, ciphertext1, ciphertext2)
}
