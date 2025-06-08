/// A Keccak Item
/// This holds the internal state and depends on the architecture.
pub(crate) trait KeccakStateItem<const N: usize>: internal::KeccakItem<N> {}

// Implement the public trait for all items.
impl<const N: usize, T: internal::KeccakItem<N>> KeccakStateItem<N> for T {}

// XXX: These should be default functions on `KeccakStateItem`, but hax doesn't
//      support that yet. cryspen/hax#888
#[inline(always)]
pub(crate) fn get_ij<const N: usize, T: KeccakStateItem<N>>(
    arr: &[T; 25],
    i: usize,
    j: usize,
) -> &T {
    &arr[5 * j + i]
}

#[inline(always)]
pub(crate) fn set_ij<const N: usize, T: KeccakStateItem<N>>(
    arr: &mut [T; 25],
    i: usize,
    j: usize,
    value: T,
) {
    arr[5 * j + i] = value;
}

pub(crate) mod internal {
    /// A trait for multiplexing implementations.
    pub trait KeccakItem<const N: usize>: Clone + Copy {
        /// Zero
        fn zero() -> Self;

        /// `a ^ b ^ c ^ d ^ e`
        fn xor5(a: Self, b: Self, c: Self, d: Self, e: Self) -> Self;

        /// `a ^ (b <<< 1)``
        fn rotate_left1_and_xor(a: Self, b: Self) -> Self;

        /// `(a ^ b) <<< LEFT`
        fn xor_and_rotate<const LEFT: i32, const RIGHT: i32>(a: Self, b: Self) -> Self;

        /// `a ^ (b & !c)`
        fn and_not_xor(a: Self, b: Self, c: Self) -> Self;

        /// `a ^ c`
        fn xor_constant(a: Self, c: u64) -> Self;

        /// `a ^ b`
        fn xor(a: Self, b: Self) -> Self;

        /// Load a block
        fn load_block<const RATE: usize>(state: &mut [Self; 25], input: &[&[u8]; N], start: usize);

        /// Load the last block
        fn load_last<const RATE: usize, const DELIMITER: u8>(
            state: &mut [Self; 25],
            input: &[&[u8]; N],
            start: usize,
            len: usize,
        );

        /// Store blocks
        fn store_block<const RATE: usize>(
            state: &[Self; 25],
            input: &mut [&mut [u8]; N],
            start: usize,
            len: usize,
        );
    }
}
