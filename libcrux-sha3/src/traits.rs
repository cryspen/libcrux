/// A Keccak Item
/// This holds the internal state and depends on the architecture.
pub trait KeccakStateItem<'a, const N: usize>: internal::KeccakItem<'a, N> {}

// Implement the public trait for all items.
impl<'a, const N: usize, T: internal::KeccakItem<'a, N>> KeccakStateItem<'a, N> for T {}

pub(crate) mod internal {
    /// A trait for multiplexing implementations.
    pub trait KeccakItem<'a, const N: usize>: Clone + Copy {
        type B: Buffer;
        type Bm: BufferMut;
        type Bl: Block<Self::B, Self::Bm>;

        fn zero() -> Self;
        fn xor5(a: Self, b: Self, c: Self, d: Self, e: Self) -> Self;
        fn rotate_left1_and_xor(a: Self, b: Self) -> Self;
        fn xor_and_rotate<const LEFT: i32, const RIGHT: i32>(a: Self, b: Self) -> Self;
        fn and_not_xor(a: Self, b: Self, c: Self) -> Self;
        fn xor_constant(a: Self, c: u64) -> Self;
        fn xor(a: Self, b: Self) -> Self;
        fn load_block<const BLOCKSIZE: usize>(state: &mut [[Self; 5]; 5], buf: Self::B);
        fn store_block<const BLOCKSIZE: usize>(a: &[[Self; 5]; 5], b: Self::Bm);
        fn load_block_full<const BLOCKSIZE: usize>(state: &mut [[Self; 5]; 5], block: Self::Bl);
        fn store_block_full<const BLOCKSIZE: usize>(state: &[[Self; 5]; 5]) -> Self::Bl;
        fn split_at_mut_n(a: [&mut [u8]; N], mid: usize) -> ([&mut [u8]; N], [&mut [u8]; N]);
    }

    /// A buffer.
    /// This is depending on the implementation multiple lanes.
    pub trait Buffer: Clone + Copy {
        fn len(&self) -> usize;
        fn slice(&self, start: usize, len: usize) -> Self;
    }

    /// An output (mutable) buffer.
    /// This is depending on the implementation multiple lanes.
    pub trait BufferMut {
        fn len(&self) -> usize;
        fn slice_mut(self, mid: usize) -> (Self, Self)
        where
            Self: Sized;
    }

    /// A full, owning block.
    /// This is used for the final absorb instead of the [`Buffer`].
    pub trait Block<B: Buffer, Bm: BufferMut>: Clone + Copy {
        fn init(b: B) -> Self;
        fn set_constants<const DELIM: u8, const EOB: usize>(&mut self);
        fn to_bytes(self, out: Bm);
    }
}
