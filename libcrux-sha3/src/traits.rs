use hax_lib;

// XXX: These should be default functions on `KeccakItem`, but hax doesn't
//      support that yet. cryspen/hax#888
#[cfg_attr(hax, hax_lib::requires(i < 5 && j < 5))]
#[inline(always)]
pub(crate) fn get_ij<const N: usize, T: KeccakItem<N>>(arr: &[T; 25], i: usize, j: usize) -> &T {
    &arr[5 * j + i]
}

#[cfg_attr(hax, hax_lib::requires(i < 5 && j < 5))]
#[inline(always)]
pub(crate) fn set_ij<const N: usize, T: KeccakItem<N>>(
    arr: &mut [T; 25],
    i: usize,
    j: usize,
    value: T,
) {
    arr[5 * j + i] = value;
}

/// A Keccak Item for multiplexing arithmetic implementations.
#[hax_lib::attributes]
pub(crate) trait KeccakItem<const N: usize>: Clone + Copy {
    /// Zero
    #[hax_lib::requires(true)]
    fn zero() -> Self;

    /// `a ^ b ^ c ^ d ^ e`
    #[hax_lib::requires(true)]
    fn xor5(a: Self, b: Self, c: Self, d: Self, e: Self) -> Self;

    /// `a ^ (b <<< 1)``
    #[hax_lib::requires(true)]
    fn rotate_left1_and_xor(a: Self, b: Self) -> Self;

    /// `(a ^ b) <<< LEFT`
    #[hax_lib::requires(true)]
    fn xor_and_rotate<const LEFT: i32, const RIGHT: i32>(a: Self, b: Self) -> Self;

    /// `a ^ (b & !c)`
    #[hax_lib::requires(true)]
    fn and_not_xor(a: Self, b: Self, c: Self) -> Self;

    /// `a ^ c`
    #[hax_lib::requires(true)]
    fn xor_constant(a: Self, c: u64) -> Self;

    /// `a ^ b`
    #[hax_lib::requires(true)]
    fn xor(a: Self, b: Self) -> Self;
}

/// Trait to load new bytes into the state.
pub(crate) trait Absorb<const N: usize> {
    /// Absorb a block
    fn load_block<const RATE: usize>(&mut self, input: &[&[u8]; N], start: usize);

    /// Absorb the last block (may be partial)
    fn load_last<const RATE: usize, const DELIMITER: u8>(
        &mut self,
        input: &[&[u8]; N],
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
#[hax_lib::fstar::replace(
    interface,
    "
class t_Squeeze1 (v_Self: Type0) (v_T: Type0) = {
  f_squeeze_pre:v_RATE: usize -> v_Self -> t_Slice u8 -> usize -> usize -> Type0;
  f_squeeze_post:v_RATE: usize -> v_Self -> t_Slice u8 -> usize -> usize -> t_Slice u8 -> Type0;
  f_squeeze:v_RATE: usize -> x0: v_Self -> x1: t_Slice u8 -> x2: usize -> x3: usize
    -> Prims.Pure (t_Slice u8)
        (f_squeeze_pre v_RATE x0 x1 x2 x3)
        (fun result -> f_squeeze_post v_RATE x0 x1 x2 x3 result)
}
"
)]
pub(crate) trait Squeeze1<T: KeccakItem<1>> {
    fn squeeze<const RATE: usize>(&self, out: &mut [u8], start: usize, len: usize);
}

/// Trait to squeeze bytes out of the state.
///
/// Note that this is implemented for each platform (1, 2, 4) because hax can't
/// handle the mutability required for a generic implementation.
///
/// Store blocks `N = 2`
#[cfg(feature = "simd128")]
pub(crate) trait Squeeze2<T: KeccakItem<2>> {
    fn squeeze2<const RATE: usize>(
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
