use core::arch::aarch64::*;

// This file optimizes for the stable Rust Neon Intrinsics
// If we want to use the unstable neon-sha3 instructions, we could use:
// veor3q_u64, vrax1q_u64, vxarq_u64, and vbcaxq_u64
// These instructions might speed up our code even more.


/// Incremental state
#[cfg_attr(hax, hax_lib::opaque_type)]
#[derive(Clone, Copy)]
pub struct KeccakStateX2 {
    pub st: [[uint64x2_t; 5]; 5],
}

#[inline(always)]
fn rotate_left<const LEFT:i32, const RIGHT:i32>(x:uint64x2_t) -> uint64x2_t {
    debug_assert!(LEFT+RIGHT == 64);
    //unsafe { vsriq_n_u64::<RIGHT>(vshlq_n_u64::<LEFT>(x), x) }
    unsafe { veorq_u64(vshlq_n_u64::<LEFT>(x), vshrq_n_u64::<RIGHT>(x)) }
}


impl KeccakStateX2 {
    /// Create a new Shake128 x4 state.
    #[inline(always)]
    pub(crate)  fn new() -> Self {
        unsafe{
            Self {
                st: [[vdupq_n_u64(0); 5]; 5],
            }
        }
    }
}
    
#[inline(always)]
fn theta(s: &mut KeccakStateX2) {
    let mut c : [uint64x2_t; 5] = unsafe {[vdupq_n_u64(0); 5]};
    for i in 0..5 {
        c[i] = unsafe {veorq_u64(s.st[0][i],veorq_u64(s.st[1][i],
                        veorq_u64(s.st[2][i],veorq_u64(s.st[3][i],s.st[4][i]))))};
        // Needs nightly
        //  c[i] = unsafe {veor3q_u64(s.st[0][i],s.st[1][i],
        //                   veor3q_u64(s.st[2][i],s.st[3][i],s.st[4][i]))};
    }
    
    for i in 0..5 {
        let t = unsafe { veorq_u64(c[(i + 4) % 5], rotate_left::<1,63>(c[(i+1)%5])) };
        // Needs nightly
        // let t = unsafe { vrax1q_u64(c[(i+4)%5], c[(i+1)%5]) };
        for j in 0..5 {
            s.st[j][i] = unsafe {veorq_u64(s.st[j][i],t)};
        }
    }
}

const _ROTC: [usize;24] = 
    [1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,];

#[inline(always)]
fn rho(s: &mut KeccakStateX2) {
    // If combined with theta, we could use Nightly: vxarq_u64
    s.st[0][0] = s.st[0][0];
    s.st[0][1] = rotate_left::<1,63>(s.st[0][1]);
    s.st[0][2] = rotate_left::<62,2>(s.st[0][2]);
    s.st[0][3] = rotate_left::<28,36>(s.st[0][3]);
    s.st[0][4] = rotate_left::<27,37>(s.st[0][4]);
    s.st[1][0] = rotate_left::<36,28>(s.st[1][0]);
    s.st[1][1] = rotate_left::<44,20>(s.st[1][1]);
    s.st[1][2] = rotate_left::<6,58>(s.st[1][2]);
    s.st[1][3] = rotate_left::<55,9>(s.st[1][3]);
    s.st[1][4] = rotate_left::<20,44>(s.st[1][4]);
    s.st[2][0] = rotate_left::<3,61>(s.st[2][0]);
    s.st[2][1] = rotate_left::<10,54>(s.st[2][1]);
    s.st[2][2] = rotate_left::<43,21>(s.st[2][2]);
    s.st[2][3] = rotate_left::<25,39>(s.st[2][3]);
    s.st[2][4] = rotate_left::<39,25>(s.st[2][4]);
    s.st[3][0] = rotate_left::<41,23>(s.st[3][0]);
    s.st[3][1] = rotate_left::<45,19>(s.st[3][1]);
    s.st[3][2] = rotate_left::<15,49>(s.st[3][2]);
    s.st[3][3] = rotate_left::<21,43>(s.st[3][3]);
    s.st[3][4] = rotate_left::<8,56>(s.st[3][4]);
    s.st[4][0] = rotate_left::<18,46>(s.st[4][0]);
    s.st[4][1] = rotate_left::<2,62>(s.st[4][1]);
    s.st[4][2] = rotate_left::<61,3>(s.st[4][2]);
    s.st[4][3] = rotate_left::<56,8>(s.st[4][3]);
    s.st[4][4] = rotate_left::<14,50>(s.st[4][4]);
}


const _PI : [usize;24] = [
    6, 12, 18, 24, 3, 9, 10, 16, 22, 1, 7, 13, 19, 20, 4, 5, 11, 17, 23, 2, 8, 14, 15, 21,
];

#[inline(always)]
fn pi(s: &mut KeccakStateX2) {
    let old = s.st.clone();
    s.st[0][1] = old[1][1];
    s.st[0][2] = old[2][2];
    s.st[0][3] = old[3][3];
    s.st[0][4] = old[4][4];
    s.st[1][0] = old[0][3];
    s.st[1][1] = old[1][4];
    s.st[1][2] = old[2][0];
    s.st[1][3] = old[3][1];
    s.st[1][4] = old[4][2];
    s.st[2][0] = old[0][1];
    s.st[2][1] = old[1][2];
    s.st[2][2] = old[2][3];
    s.st[2][3] = old[3][4];
    s.st[2][4] = old[4][0];
    s.st[3][0] = old[0][4];
    s.st[3][1] = old[1][0];
    s.st[3][2] = old[2][1];
    s.st[3][3] = old[3][2];
    s.st[3][4] = old[4][3];
    s.st[4][0] = old[0][2];
    s.st[4][1] = old[1][3];
    s.st[4][2] = old[2][4];
    s.st[4][3] = old[3][0];
    s.st[4][4] = old[4][1];
}

#[inline(always)]
fn chi(s: &mut KeccakStateX2) {
    let mut c : [uint64x2_t; 5] = unsafe {[vdupq_n_u64(0); 5]};
    for i in 0..5 {
        for j in 0..5 {
            c[j] = s.st[i][j]
        }
        for j in 0..5 {
            s.st[i][j] = unsafe{ veorq_u64(s.st[i][j], vbicq_u64(c[(j + 2) % 5], c[(j + 1) % 5])) };
            // Needs nightly
            //s.st[i][j] = unsafe{ vbcaxq_u64(s.st[i][j], c[(j + 2) % 5], c[(j + 1) % 5]) };
        }
    }
}

const ROUNDCONSTANTS: [u64;24] = [
    0x0000_0000_0000_0001u64,  0x0000_0000_0000_8082u64,  0x8000_0000_0000_808au64,
    0x8000_0000_8000_8000u64,  0x0000_0000_0000_808bu64,  0x0000_0000_8000_0001u64,
    0x8000_0000_8000_8081u64,  0x8000_0000_0000_8009u64,  0x0000_0000_0000_008au64,
    0x0000_0000_0000_0088u64,  0x0000_0000_8000_8009u64,  0x0000_0000_8000_000au64,
    0x0000_0000_8000_808bu64,  0x8000_0000_0000_008bu64,  0x8000_0000_0000_8089u64,
    0x8000_0000_0000_8003u64,  0x8000_0000_0000_8002u64,  0x8000_0000_0000_0080u64,
    0x0000_0000_0000_800au64,  0x8000_0000_8000_000au64,  0x8000_0000_8000_8081u64,
    0x8000_0000_0000_8080u64,  0x0000_0000_8000_0001u64,  0x8000_0000_8000_8008u64,
];

#[inline(always)]
fn iota(s: &mut KeccakStateX2, round:usize) {
    let c = unsafe { vdupq_n_u64(ROUNDCONSTANTS[round]) };
    s.st[0][0] = unsafe { veorq_u64(s.st[0][0], c) };
}

#[inline(always)]
pub(crate) fn keccakf1600(s: &mut KeccakStateX2) {
    for i in 0..24 {
        theta(s);
        rho(s);
        pi(s);
        chi(s);
        iota(s, i);
    }
}

#[inline(always)]
pub(crate) fn absorb_block2<const RATE:usize>(s: &mut KeccakStateX2, block0: &[u8], block1: &[u8]) {
    debug_assert!(RATE == block0.len() && RATE == block1.len() && RATE % 8 == 0);
    for i in 0..RATE/16 {
        let v0 = unsafe { vld1q_u64(block0[16*i..(16*i)+16].as_ptr() as *const u64) };
        let v1 = unsafe { vld1q_u64(block1[16*i..(16*i)+16].as_ptr() as *const u64) };
        s.st[(2*i)/5][(2*i)%5] = unsafe { veorq_u64(s.st[(2*i)/5][(2*i)%5], vtrn1q_u64(v0,v1)) };
        s.st[(2*i+1)/5][(2*i+1)%5] = unsafe { veorq_u64(s.st[(2*i+1)/5][(2*i+1)%5], vtrn2q_u64(v0,v1)) };
    }
    if RATE%16 != 0 {
        let i = (RATE/8 - 1)/5;
        let j = (RATE/8 - 1)%5;
        let mut u = [0u64; 2];
        u[0] = u64::from_le_bytes(block0[RATE-8..].try_into().unwrap());
        u[1] = u64::from_le_bytes(block1[RATE-8..].try_into().unwrap());
        let uvec = unsafe { vld1q_u64(u.as_ptr() as *const u64) };
        s.st[i][j] = unsafe { veorq_u64(s.st[i][j], uvec)};
    }
    keccakf1600(s)
}

#[inline(always)]
pub(crate) fn absorb_final2<const RATE:usize, const DELIM:u8>(s: &mut KeccakStateX2, last0: &[u8], last1: &[u8]) {
    debug_assert!(last0.len() == last1.len() && last0.len() < RATE);
    let mut b0 = [0u8; 200];
    let mut b1 = [0u8; 200];
    b0[0..last0.len()].copy_from_slice(last0);
    b1[0..last1.len()].copy_from_slice(last1);
    b0[last0.len()] = DELIM;
    b0[RATE-1] = b0[RATE-1] | 128u8;
    b1[last1.len()] = DELIM;
    b1[RATE-1] = b1[RATE-1] | 128u8;
    absorb_block2::<RATE>(s, &b0[0..RATE], &b1[0..RATE])
}

#[inline(always)]
pub(crate) fn squeeze2<const RATE:usize>(s: &KeccakStateX2, out0: &mut [u8], out1: &mut [u8]) {
    for i in 0..RATE/16 {
        let v0 = unsafe { vtrn1q_u64(s.st[(2*i)/5][(2*i)%5], s.st[(2*i+1)/5][(2*i+1)%5]) };
        let v1 = unsafe { vtrn2q_u64(s.st[(2*i)/5][(2*i)%5], s.st[(2*i+1)/5][(2*i+1)%5]) };
        unsafe { vst1q_u64(out0[16*i..16*i+16].as_mut_ptr() as *mut u64, v0) };
        unsafe { vst1q_u64(out1[16*i..16*i+16].as_mut_ptr() as *mut u64, v1) };
    }
    if RATE%16 != 0 {
        debug_assert!(RATE % 8 == 0);
        let i = (RATE/8 - 1)/5;
        let j = (RATE/8 - 1)%5;
        let mut u = [0u8;16];
        unsafe { vst1q_u64(u.as_mut_ptr() as *mut u64, s.st[i][j])};
        out0[RATE-8..RATE].copy_from_slice(&u[0..8]);
        out1[RATE-8..RATE].copy_from_slice(&u[8..16]);
    }
}   