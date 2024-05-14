mod sha3_generic;
mod sha3_portable;
mod sha3_trait;
pub use sha3_generic::*;

pub type KeccakState1 = KeccakState<1, u64>;
#[inline(always)]
fn keccakx1<const RATE: usize, const DELIM: u8>(data: [&[u8]; 1], out: [&mut [u8]; 1]) {
    keccak::<1, u64, RATE, DELIM>(data, out)
}

#[cfg(feature = "simd128")]
mod sha3_arm64;
#[cfg(feature = "simd128")]
pub type KeccakState2 = KeccakState<2, core::arch::aarch64::uint64x2_t>;
#[cfg(feature = "simd128")]
#[inline(always)]
fn keccakx2<const RATE: usize, const DELIM: u8>(data: [&[u8]; 2], out: [&mut [u8]; 2]) {
    keccak::<2, core::arch::aarch64::uint64x2_t, RATE, DELIM>(data, out)
}
#[cfg(feature = "simd128")]
pub type KeccakState4 = [KeccakState2; 2];

#[cfg(feature = "simd256")]
mod sha3_avx2;
#[cfg(feature = "simd256")]
#[inline(always)]
fn keccakx4<const RATE: usize, const DELIM: u8>(data: [&[u8]; 4], out: [&mut [u8]; 4]) {
    keccak::<4, core::arch::x86_64::__m256i, RATE, DELIM>(data, out)
}
#[cfg(feature = "simd256")]
pub type KeccakState4 = KeccakState<4, core::arch::x86_64::__m256i>;

#[cfg(not(any(feature = "simd128", feature = "simd256")))]
pub type KeccakState2 = [KeccakState1; 2];
#[cfg(not(any(feature = "simd128", feature = "simd256")))]
pub type KeccakState4 = [KeccakState1; 4];

#[cfg(feature = "simd128")]
pub fn sha3_224(data: &[u8]) -> [u8; 28] {
    let mut d0 = [0u8; 28];
    let mut d1 = [0u8; 28];
    keccakx2::<144, 0x06u8>([data, data], [&mut d0, &mut d1]);
    d0
}
#[cfg(not(feature = "simd128"))]
pub fn sha3_224(data: &[u8]) -> [u8; 28] {
    let mut d0 = [0u8; 28];
    keccakx1::<144, 0x06u8>([data], [&mut d0]);
    d0
}

#[cfg(feature = "simd128")]
pub fn sha3_256(data: &[u8]) -> [u8; 32] {
    let mut d0 = [0u8; 32];
    let mut d1 = [0u8; 32];
    keccakx2::<136, 0x06u8>([data, data], [&mut d0, &mut d1]);
    d0
}

#[cfg(feature = "simd256")]
pub fn sha3_256(data: &[u8]) -> [u8; 32] {
    let mut d0 = [0u8; 32];
    let mut d1 = [0u8; 32];
    let mut d2 = [0u8; 32];
    let mut d3 = [0u8; 32];
    keccakx4::<136, 0x06u8>(
        [data, data, data, data],
        [&mut d0, &mut d1, &mut d2, &mut d3],
    );
    d0
}

pub fn sha3_256_portable(data: &[u8]) -> [u8; 32] {
    let mut d0 = [0u8; 32];
    keccakx1::<136, 0x06u8>([data], [&mut d0]);
    d0
}

#[cfg(feature = "simd128")]
pub fn sha3_384(data: &[u8]) -> [u8; 48] {
    let mut d0 = [0u8; 48];
    let mut d1 = [0u8; 48];
    keccakx2::<104, 0x06u8>([data, data], [&mut d0, &mut d1]);
    d0
}
#[cfg(not(feature = "simd128"))]
pub fn sha3_384(data: &[u8]) -> [u8; 48] {
    let mut d0 = [0u8; 48];
    keccakx1::<104, 0x06u8>([data], [&mut d0]);
    d0
}

#[cfg(feature = "simd128")]
pub fn sha3_512(data: &[u8]) -> [u8; 64] {
    let mut d0 = [0u8; 64];
    let mut d1 = [0u8; 64];
    keccakx2::<72, 0x06u8>([data, data], [&mut d0, &mut d1]);
    d0
}

#[cfg(feature = "simd256")]
pub fn sha3_512(data: &[u8]) -> [u8; 64] {
    let mut d0 = [0u8; 64];
    let mut d1 = [0u8; 64];
    let mut d2 = [0u8; 64];
    let mut d3 = [0u8; 64];
    keccakx4::<72, 0x06u8>(
        [data, data, data, data],
        [&mut d0, &mut d1, &mut d2, &mut d3],
    );
    d0
}

pub fn sha3_512_portable(data: &[u8]) -> [u8; 64] {
    let mut d0 = [0u8; 64];
    keccakx1::<72, 0x06u8>([data], [&mut d0]);
    d0
}

#[cfg(feature = "simd128")]
pub fn shake128<const LEN: usize>(data: &[u8]) -> [u8; LEN] {
    let mut d0 = [0u8; LEN];
    let mut d1 = [0u8; LEN];
    keccakx2::<168, 0x1fu8>([data, data], [&mut d0, &mut d1]);
    d0
}
#[cfg(not(feature = "simd128"))]
pub fn shake128<const LEN: usize>(data: &[u8]) -> [u8; LEN] {
    let mut d0 = [0u8; LEN];
    keccakx1::<168, 0x1fu8>([data], [&mut d0]);
    d0
}

#[cfg(feature = "simd128")]
pub fn shake256<const LEN: usize>(data: &[u8]) -> [u8; LEN] {
    let mut d0 = [0u8; LEN];
    let mut d1 = [0u8; LEN];
    keccakx2::<136, 0x1fu8>([data, data], [&mut d0, &mut d1]);
    d0
}
#[cfg(not(feature = "simd128"))]
pub fn shake256<const LEN: usize>(data: &[u8]) -> [u8; LEN] {
    let mut d0 = [0u8; LEN];
    keccakx1::<136, 0x1fu8>([data], [&mut d0]);
    d0
}

#[cfg(feature = "simd128")]
pub fn shake256x2(input0: &[u8], input1: &[u8], out0: &mut [u8], out1: &mut [u8]) {
    keccakx2::<136, 0x1fu8>([input0, input1], [out0, out1]);
}
#[cfg(not(feature = "simd128"))]
pub fn shake256x2(input0: &[u8], input1: &[u8], out0: &mut [u8], out1: &mut [u8]) {
    keccakx1::<136, 0x1fu8>([input0], [out0]);
    keccakx1::<136, 0x1fu8>([input1], [out1]);
}

#[cfg(feature = "simd256")]
pub fn shake256x4(
    input0: &[u8],
    input1: &[u8],
    input2: &[u8],
    input3: &[u8],
    out0: &mut [u8],
    out1: &mut [u8],
    out2: &mut [u8],
    out3: &mut [u8],
) {
    keccak::<4, core::arch::x86_64::__m256i, 136, 0x1fu8>(
        [input0, input1, input2, input3],
        [out0, out1, out2, out3],
    );
}
#[cfg(feature = "simd128")]
pub fn shake256x4(
    input0: &[u8],
    input1: &[u8],
    input2: &[u8],
    input3: &[u8],
    out0: &mut [u8],
    out1: &mut [u8],
    out2: &mut [u8],
    out3: &mut [u8],
) {
    keccakx2::<136, 0x1fu8>([input0, input1], [out0, out1]);
    keccakx2::<136, 0x1fu8>([input2, input3], [out2, out3]);
}
#[cfg(not(any(feature = "simd128", feature = "simd256")))]
pub fn shake256x4(
    input0: &[u8],
    input1: &[u8],
    input2: &[u8],
    input3: &[u8],
    out0: &mut [u8],
    out1: &mut [u8],
    out2: &mut [u8],
    out3: &mut [u8],
) {
    keccakx1::<136, 0x1fu8>([input0], [out0]);
    keccakx1::<136, 0x1fu8>([input1], [out1]);
    keccakx1::<136, 0x1fu8>([input2], [out2]);
    keccakx1::<136, 0x1fu8>([input3], [out3]);
}

/// Incremental API

pub fn shake128_init() -> KeccakState1 {
    KeccakState1::new()
}

pub fn shake128_absorb_final(s: &mut KeccakState1, data0: &[u8]) {
    absorb_final::<1, u64, 168, 0x1fu8>(s, [data0]);
}

pub fn shake128_squeeze_first_three_blocks(s: &mut KeccakState1, out0: &mut [u8]) {
    squeeze_first_three_blocks::<1, u64, 168>(s, [out0])
}

pub fn shake128_squeeze_next_block(s: &mut KeccakState1, out0: &mut [u8]) {
    squeeze_next_block::<1, u64, 168>(s, [out0])
}

#[cfg(feature = "simd128")]
pub fn shake128x2_init() -> KeccakState2 {
    KeccakState2::new()
}
#[cfg(not(any(feature = "simd128", feature = "simd256")))]
pub fn shake128x2_init() -> KeccakState2 {
    let s0 = KeccakState1::new();
    let s1 = KeccakState1::new();
    [s0, s1]
}

#[cfg(feature = "simd128")]
pub fn shake128x2_absorb_final(s: &mut KeccakState2, data0: &[u8], data1: &[u8]) {
    absorb_final::<2, core::arch::aarch64::uint64x2_t, 168, 0x1fu8>(s, [data0, data1]);
}
#[cfg(not(any(feature = "simd128", feature = "simd256")))]
pub fn shake128x2_absorb_final(s: &mut KeccakState2, data0: &[u8], data1: &[u8]) {
    let [mut s0, mut s1] = s;
    shake128_absorb_final(&mut s0, data0);
    shake128_absorb_final(&mut s1, data1);
}

#[cfg(feature = "simd128")]
pub fn shake128x2_squeeze_first_three_blocks(
    s: &mut KeccakState2,
    out0: &mut [u8],
    out1: &mut [u8],
) {
    squeeze_first_three_blocks::<2, core::arch::aarch64::uint64x2_t, 168>(s, [out0, out1])
}
#[cfg(not(any(feature = "simd128", feature = "simd256")))]
pub fn shake128x2_squeeze_first_three_blocks(
    s: &mut KeccakState2,
    out0: &mut [u8],
    out1: &mut [u8],
) {
    let [mut s0, mut s1] = s;
    shake128_squeeze_first_three_blocks(&mut s0, out0);
    shake128_squeeze_first_three_blocks(&mut s1, out1);
}

#[cfg(feature = "simd128")]
pub fn shake128x2_squeeze_next_block(s: &mut KeccakState2, out0: &mut [u8], out1: &mut [u8]) {
    squeeze_next_block::<2, core::arch::aarch64::uint64x2_t, 168>(s, [out0, out1])
}
#[cfg(not(any(feature = "simd128", feature = "simd256")))]
pub fn shake128x2_squeeze_next_block(s: &mut KeccakState2, out0: &mut [u8], out1: &mut [u8]) {
    let [mut s0, mut s1] = s;
    shake128_squeeze_next_block(&mut s0, out0);
    shake128_squeeze_next_block(&mut s1, out1);
}

#[cfg(feature = "simd256")]
pub fn shake128x4_init() -> KeccakState4 {
    KeccakState4::new()
}
#[cfg(feature = "simd128")]
pub fn shake128x4_init() -> KeccakState4 {
    let s0 = KeccakState2::new();
    let s1 = KeccakState2::new();
    [s0, s1]
}
#[cfg(not(any(feature = "simd128", feature = "simd256")))]
pub fn shake128x4_init() -> KeccakState4 {
    let s0 = KeccakState1::new();
    let s1 = KeccakState1::new();
    let s2 = KeccakState1::new();
    let s3 = KeccakState1::new();
    [s0, s1, s2, s3]
}

#[cfg(feature = "simd128")]
pub fn shake128x4_absorb_final(
    s: &mut KeccakState4,
    data0: &[u8],
    data1: &[u8],
    data2: &[u8],
    data3: &[u8],
) {
    absorb_final::<4, core::arch::x86_64::__m256i, 168, 0x1fu8>(s, [data0, data1, data2, data3]);
}
#[cfg(feature = "simd128")]
pub fn shake128x4_absorb_final(
    s: &mut KeccakState4,
    data0: &[u8],
    data1: &[u8],
    data2: &[u8],
    data3: &[u8],
) {
    let [mut s0, mut s1] = s;
    absorb_final::<2, core::arch::aarch64::uint64x2_t, 168, 0x1fu8>(&mut s0, [data0, data1]);
    absorb_final::<2, core::arch::aarch64::uint64x2_t, 168, 0x1fu8>(&mut s1, [data2, data3]);
}
#[cfg(not(any(feature = "simd128", feature = "simd256")))]
pub fn shake128x4_absorb_final(
    s: &mut KeccakState4,
    data0: &[u8],
    data1: &[u8],
    data2: &[u8],
    data3: &[u8],
) {
    let [mut s0, mut s1, mut s2, mut s3] = s;
    shake128_absorb_final(&mut s0, data0);
    shake128_absorb_final(&mut s1, data1);
    shake128_absorb_final(&mut s2, data2);
    shake128_absorb_final(&mut s3, data3);
}

#[cfg(feature = "simd256")]
pub fn shake128x4_squeeze_first_three_blocks(
    s: &mut KeccakState4,
    out0: &mut [u8],
    out1: &mut [u8],
    out2: &mut [u8],
    out3: &mut [u8],
) {
    squeeze_first_three_blocks::<4, core::arch::x86_64::__m256i, 168>(s, [out0, out1, out2, out3]);
}
#[cfg(feature = "simd128")]
pub fn shake128x4_squeeze_first_three_blocks(
    s: &mut KeccakState4,
    out0: &mut [u8],
    out1: &mut [u8],
    out2: &mut [u8],
    out3: &mut [u8],
) {
    let [mut s0, mut s1] = s;
    squeeze_first_three_blocks::<2, core::arch::aarch64::uint64x2_t, 168>(&mut s0, [out0, out1]);
    squeeze_first_three_blocks::<2, core::arch::aarch64::uint64x2_t, 168>(&mut s1, [out2, out3]);
}
#[cfg(not(any(feature = "simd128", feature = "simd256")))]
pub fn shake128x4_squeeze_first_three_blocks(
    s: &mut KeccakState4,
    out0: &mut [u8],
    out1: &mut [u8],
    out2: &mut [u8],
    out3: &mut [u8],
) {
    let [mut s0, mut s1, mut s2, mut s3] = s;
    shake128_squeeze_first_three_blocks(&mut s0, out0);
    shake128_squeeze_first_three_blocks(&mut s1, out1);
    shake128_squeeze_first_three_blocks(&mut s2, out2);
    shake128_squeeze_first_three_blocks(&mut s3, out3);
}

#[cfg(feature = "simd128")]
pub fn shake128x4_squeeze_next_block(
    s: &mut KeccakState4,
    out0: &mut [u8],
    out1: &mut [u8],
    out2: &mut [u8],
    out3: &mut [u8],
) {
    squeeze_next_block::<4, core::arch::x86_64::__m256i, 168>(&mut s0, [out0, out1, out2, out3]);
}
#[cfg(feature = "simd128")]
pub fn shake128x4_squeeze_next_block(
    s: &mut KeccakState4,
    out0: &mut [u8],
    out1: &mut [u8],
    out2: &mut [u8],
    out3: &mut [u8],
) {
    let [mut s0, mut s1] = s;
    squeeze_next_block::<2, core::arch::aarch64::uint64x2_t, 168>(&mut s0, [out0, out1]);
    squeeze_next_block::<2, core::arch::aarch64::uint64x2_t, 168>(&mut s1, [out2, out3]);
}
#[cfg(not(any(feature = "simd128", feature = "simd256")))]
pub fn shake128x4_squeeze_next_block(
    s: &mut KeccakState4,
    out0: &mut [u8],
    out1: &mut [u8],
    out2: &mut [u8],
    out3: &mut [u8],
) {
    let [mut s0, mut s1, mut s2, mut s3] = s;
    shake128_squeeze_next_block(&mut s0, out0);
    shake128_squeeze_next_block(&mut s1, out1);
    shake128_squeeze_next_block(&mut s2, out2);
    shake128_squeeze_next_block(&mut s3, out3);
}
