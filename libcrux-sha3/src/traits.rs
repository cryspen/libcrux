// XXX: These should be default functions on `KeccakItem`, but hax doesn't
//      support that yet. cryspen/hax#888
#[inline(always)]
pub(crate) fn get_ij<const N: usize, T: KeccakItem<N>>(arr: &[T; 25], i: usize, j: usize) -> &T {
    &arr[5 * j + i]
}

#[inline(always)]
pub(crate) fn set_ij<const N: usize, T: KeccakItem<N>>(
    arr: &mut [T; 25],
    i: usize,
    j: usize,
    value: T,
) {
    arr[5 * j + i] = value;
}

/// A Keccak Item for multiplexing implementations.
///
/// This holds the internal state and depends on the architecture.
pub(crate) trait KeccakItem<const N: usize>: Clone + Copy {
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
}

pub(crate) trait Squeeze<const N: usize, T: KeccakItem<N>> {
    /// Store blocks `N = 1`
    fn squeeze1<const RATE: usize>(&self, out: &mut [u8], start: usize, len: usize);

    /// Store blocks `N = 2`
    fn squeeze2<const RATE: usize>(
        &self,
        out0: &mut [u8],
        out1: &mut [u8],
        start: usize,
        len: usize,
    );

    /// Store blocks `N = 4`
    fn squeeze4<const RATE: usize>(
        &self,
        out0: &mut [u8],
        out1: &mut [u8],
        out2: &mut [u8],
        out3: &mut [u8],
        start: usize,
        len: usize,
    );
}
