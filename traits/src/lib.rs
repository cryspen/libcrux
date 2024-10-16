// XXX: rename to vector operations

/// Vector operations for ML-KEM
pub trait Operations: Copy + Clone {
    #[allow(non_snake_case)]
    fn ZERO() -> Self;

    fn from_i16_array(array: &[i16]) -> Self;
    fn to_i16_array(x: Self) -> [i16; 16];

    // Basic arithmetic
    fn add(lhs: Self, rhs: &Self) -> Self;
    fn sub(lhs: Self, rhs: &Self) -> Self;
    fn multiply_by_constant(v: Self, c: i16) -> Self;

    // Bitwise operations
    fn bitwise_and_with_constant(v: Self, c: i16) -> Self;
    fn shift_right<const SHIFT_BY: i32>(v: Self) -> Self;
    // fn shift_left<const SHIFT_BY: i32>(v: Self) -> Self;

    // Modular operations
    fn cond_subtract_3329(v: Self) -> Self;
    fn barrett_reduce(v: Self) -> Self;
    fn montgomery_multiply_by_constant(v: Self, c: i16) -> Self;

    // Compression
    fn compress_1(v: Self) -> Self;
    fn compress<const COEFFICIENT_BITS: i32>(v: Self) -> Self;
    fn decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(v: Self) -> Self;

    // NTT
    fn ntt_layer_1_step(a: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self;
    fn ntt_layer_2_step(a: Self, zeta0: i16, zeta1: i16) -> Self;
    fn ntt_layer_3_step(a: Self, zeta: i16) -> Self;

    fn inv_ntt_layer_1_step(a: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self;
    fn inv_ntt_layer_2_step(a: Self, zeta0: i16, zeta1: i16) -> Self;
    fn inv_ntt_layer_3_step(a: Self, zeta: i16) -> Self;

    fn ntt_multiply(lhs: &Self, rhs: &Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16)
        -> Self;

    // Serialization and deserialization
    fn serialize_1(a: Self) -> [u8; 2];
    fn deserialize_1(a: &[u8]) -> Self;

    fn serialize_4(a: Self) -> [u8; 8];
    fn deserialize_4(a: &[u8]) -> Self;

    fn serialize_5(a: Self) -> [u8; 10];
    fn deserialize_5(a: &[u8]) -> Self;

    fn serialize_10(a: Self) -> [u8; 20];
    fn deserialize_10(a: &[u8]) -> Self;

    fn serialize_11(a: Self) -> [u8; 22];
    fn deserialize_11(a: &[u8]) -> Self;

    fn serialize_12(a: Self) -> [u8; 24];
    fn deserialize_12(a: &[u8]) -> Self;

    fn rej_sample(a: &[u8], out: &mut [i16]) -> usize;
}

/// Traits for avx2.
pub mod sha3 {
    /// A Keccak Item
    /// This holds the internal state and depends on the architecture.
    pub trait KeccakStateItem<const N: usize>: KeccakItem<N> {}

    // Implement the public trait for all items.
    impl<const N: usize, T: KeccakItem<N>> KeccakStateItem<N> for T {}

    /// A trait for multiplexing implementations.
    pub trait KeccakItem<const N: usize>: Clone + Copy {
        fn zero() -> Self;
        fn xor5(a: Self, b: Self, c: Self, d: Self, e: Self) -> Self;
        fn rotate_left1_and_xor(a: Self, b: Self) -> Self;
        fn xor_and_rotate<const LEFT: i32, const RIGHT: i32>(a: Self, b: Self) -> Self;
        fn and_not_xor(a: Self, b: Self, c: Self) -> Self;
        fn xor_constant(a: Self, c: u64) -> Self;
        fn xor(a: Self, b: Self) -> Self;
        fn load_block<const RATE: usize>(a: &mut [[Self; 5]; 5], b: [&[u8]; N]);
        fn store_block<const RATE: usize>(a: &[[Self; 5]; 5], b: [&mut [u8]; N]);
        fn load_block_full<const RATE: usize>(a: &mut [[Self; 5]; 5], b: [[u8; 200]; N]);
        fn store_block_full<const RATE: usize>(a: &[[Self; 5]; 5]) -> [[u8; 200]; N];
        fn slice_n(a: [&[u8]; N], start: usize, len: usize) -> [&[u8]; N];
        fn split_at_mut_n(a: [&mut [u8]; N], mid: usize) -> ([&mut [u8]; N], [&mut [u8]; N]);
        fn store<const RATE: usize>(state: &[[Self; 5]; 5], out: [&mut [u8]; N]);
    }
}
