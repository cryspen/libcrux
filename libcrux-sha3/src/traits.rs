/// A trait for multiplexing implementations.
pub trait KeccakItem<const N: usize>: Clone + Copy {
    fn zero() -> Self;
    fn xor5(a: Self, b: Self, c: Self, d: Self, e: Self) -> Self;
    fn rotate_left1_and_xor(a: Self, b: Self) -> Self;
    fn xor_and_rotate<const LEFT: i32, const RIGHT: i32>(a: Self, b: Self) -> Self;
    fn and_not_xor(a: Self, b: Self, c: Self) -> Self;
    fn xor_constant(a: Self, c: u64) -> Self;
    fn xor(a: Self, b: Self) -> Self;
    fn load_block<const BLOCKSIZE: usize>(a: &mut [[Self; 5]; 5], b: [&[u8]; N]);
    fn store_block<const BLOCKSIZE: usize>(a: &[[Self; 5]; 5], b: [&mut [u8]; N]);
    fn load_block_full<const BLOCKSIZE: usize>(a: &mut [[Self; 5]; 5], b: [[u8; 200]; N]);
    fn store_block_full<const BLOCKSIZE: usize>(a: &[[Self; 5]; 5]) -> [[u8; 200]; N];
    fn slice_n(a: [&[u8]; N], start: usize, len: usize) -> [&[u8]; N];
    fn split_at_mut_n(a: [&mut [u8]; N], mid: usize) -> ([&mut [u8]; N], [&mut [u8]; N]);
}
