mod sha3_trait;
mod sha3_arm64;
mod sha3_generic;

pub use sha3_generic::*;

pub fn sha3_224(data: &[u8]) -> [u8;28] {
    let mut d0 = [0u8; 28];
    let mut d1 = [0u8; 28];
    keccak::<2, core::arch::aarch64::uint64x2_t, 144, 0x06u8>([data, data], [&mut d0, &mut d1]);
    d0
}

pub fn sha3_256(data: &[u8]) -> [u8;32] {
    let mut d0 = [0u8; 32];
    let mut d1 = [0u8; 32];
    keccak::<2, core::arch::aarch64::uint64x2_t, 136, 0x06u8>([data, data], [&mut d0, &mut d1]);
    d0
}

pub fn sha3_384(data: &[u8]) -> [u8;48] {
    let mut d0 = [0u8; 48];
    let mut d1 = [0u8; 48];
    keccak::<2, core::arch::aarch64::uint64x2_t, 104, 0x06u8>([data, data], [&mut d0, &mut d1]);
    d0
}

pub fn sha3_512(data: &[u8]) -> [u8;64] {
    let mut d0 = [0u8; 64];
    let mut d1 = [0u8; 64];
    keccak::<2, core::arch::aarch64::uint64x2_t, 72, 0x06u8>([data, data], [&mut d0, &mut d1]);
    d0
}

pub fn shake128<const LEN:usize>(data: &[u8]) -> [u8; LEN] {
    let mut d0 = [0u8; LEN];
    let mut d1 = [0u8; LEN];
    keccak::<2, core::arch::aarch64::uint64x2_t, 168, 0x1fu8>([data, data], [&mut d0, &mut d1]);
    d0
}

pub fn shake256<const LEN:usize>(data: &[u8]) -> [u8; LEN] {
    let mut d0 = [0u8; LEN];
    let mut d1 = [0u8; LEN];
    keccak::<2, core::arch::aarch64::uint64x2_t, 136, 0x1fu8>([data, data], [&mut d0, &mut d1]);
    d0
}

pub fn shake128x2_init() -> KeccakState<2,core::arch::aarch64::uint64x2_t> {
    let s = KeccakState::new();
    s
}

pub fn shake128x2_absorb_final(s:&mut KeccakState<2,core::arch::aarch64::uint64x2_t>, data0: &[u8], data1: &[u8]) {
    absorb_final::<2,core::arch::aarch64::uint64x2_t,168, 0x1fu8>(s,[data0,data1]);
}

pub fn shake128x2_squeeze_first_three_blocks(s: &mut KeccakState<2,core::arch::aarch64::uint64x2_t>, out0:&mut [u8], out1:&mut [u8]) {
    squeeze_first_three_blocks::<2,core::arch::aarch64::uint64x2_t,168>(s, [out0, out1])
}

pub fn shake128x2_squeeze_next_block(s: &mut KeccakState<2,core::arch::aarch64::uint64x2_t>, out0: &mut [u8], out1: &mut [u8]) {
    squeeze_next_block::<2,core::arch::aarch64::uint64x2_t,168>(s, [out0, out1])
}

pub fn shake256x2(input0: &[u8], input1: &[u8], out0: &mut [u8], out1: &mut [u8]) {
    keccak::<2,core::arch::aarch64::uint64x2_t,136, 0x1fu8>([input0, input1], [out0, out1]);
}
