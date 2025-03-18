/// A Keccak Item
/// This holds the internal state and depends on the architecture.
pub trait KeccakStateItem<const N: usize>: internal::KeccakItem<N> {}

// Implement the public trait for all items.
impl<const N: usize, T: internal::KeccakItem<N>> KeccakStateItem<N> for T {}

pub(crate) fn get_ij<const N: usize, T: KeccakStateItem<N>>(
    arr: &[T; 25],
    i: usize,
    j: usize,
) -> T {
    arr[5 * j + i]
}

pub(crate) fn set_ij<const N: usize, T: KeccakStateItem<N>>(
    arr: &mut [T; 25],
    i: usize,
    j: usize,
    v: T,
) {
    arr[5 * j + i] = v;
}

pub(crate) mod internal {
    /// A trait for multiplexing implementations.
    pub trait KeccakItem<const N: usize>: Clone + Copy {
        fn zero() -> Self;
        fn xor5(a: Self, b: Self, c: Self, d: Self, e: Self) -> Self;
        fn rotate_left1_and_xor(a: Self, b: Self) -> Self;
        fn xor_and_rotate<const LEFT: i32, const RIGHT: i32>(a: Self, b: Self) -> Self;
        fn and_not_xor(a: Self, b: Self, c: Self) -> Self;
        fn xor_constant(a: Self, c: u64) -> Self;
        fn xor(a: Self, b: Self) -> Self;
        fn load_block<const RATE: usize>(state: &mut [Self; 25], blocks: &[&[u8]; N], start: usize);
        fn store_block<const RATE: usize>(state: &[Self; 25], blocks: &mut [&mut [u8]; N]);
        fn load_block_full<const RATE: usize>(
            state: &mut [Self; 25],
            blocks: &[[u8; 200]; N],
            start: usize,
        );
        fn store_block_full<const RATE: usize>(a: &[Self; 25], out: &mut [[u8; 200]; N]);
        fn split_at_mut_n(a: [&mut [u8]; N], mid: usize) -> ([&mut [u8]; N], [&mut [u8]; N]);
        fn store<const RATE: usize>(state: &[Self; 25], out: [&mut [u8]; N]);
    }
}
