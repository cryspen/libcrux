use libcrux_secrets::Secret;

// XXX: These should be default functions on `KeccakItem`, but hax doesn't
//      support that yet. cryspen/hax#888
#[inline(always)]
pub(crate) fn get_ij<const N: usize, T: KeccakItem<N>>(
    arr: &[Secret<T>; 25],
    i: usize,
    j: usize,
) -> &Secret<T> {
    &arr[5 * j + i]
}

#[inline(always)]
pub(crate) fn set_ij<const N: usize, T: KeccakItem<N>>(
    arr: &mut [Secret<T>; 25],
    i: usize,
    j: usize,
    value: Secret<T>,
) {
    arr[5 * j + i] = value;
}

/// A Keccak Item for multiplexing arithmetic implementations.
pub(crate) trait KeccakItem<const N: usize>: Clone + Copy + libcrux_secrets::Scalar {
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
}

/// Trait to load new bytes into the state.
pub(crate) trait Absorb<const N: usize> {
    /// Absorb a block
    fn load_block<const RATE: usize>(&mut self, input: &[&[Secret<u8>]; N], start: usize);

    /// Absorb the last block (may be partial)
    fn load_last<const RATE: usize, const DELIMITER: u8>(
        &mut self,
        input: &[&[Secret<u8>]; N],
        start: usize,
        len: usize,
    );
}

/// Trait to squeeze bytes out of the state.
///
/// Note that this is implemented for each platform (1, 2, 4) because hax can't
/// handle the mutability required for a generic implementation.
///
/// Store blocks `N = 1`
pub(crate) trait Squeeze1<T: KeccakItem<1>> {
    fn squeeze<const RATE: usize>(&self, out: &mut [Secret<u8>], start: usize, len: usize);
}

/// Trait to squeeze bytes out of the state.
///
/// Note that this is implemented for each platform (1, 2, 4) because hax can't
/// handle the mutability required for a generic implementation.
///
/// Store blocks `N = 2`
#[cfg(feature = "simd128")]
pub(crate) trait Squeeze2<T: KeccakItem<2>> {
    fn squeeze<const RATE: usize>(
        &self,
        out0: &mut [u8],
        out1: &mut [u8],
        start: usize,
        len: usize,
    );
}

/// Trait to squeeze bytes out of the state.
///
/// Note that this is implemented for each platform (1, 2, 4) because hax can't
/// handle the mutability required for a generic implementation.
///
/// Store blocks `N = 4`
#[cfg(feature = "simd256")]
pub(crate) trait Squeeze4<T: KeccakItem<4>> {
    fn squeeze<const RATE: usize>(
        &self,
        out0: &mut [Secret<u8>],
        out1: &mut [Secret<u8>],
        out2: &mut [Secret<u8>],
        out3: &mut [Secret<u8>],
        start: usize,
        len: usize,
    );
}
