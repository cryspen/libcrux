use core::arch::aarch64::*;

pub(crate) type State = uint8x16_t;

fn new_state() -> State {
    unsafe {vdupq_n_u8(0)}
}

fn xor_key1_state(st: &mut State, k: &State) {
    unsafe {*st = veorq_u8(*st, *k)}
}

fn aes_enc(st: &mut State, key: &State) {
    unsafe {*st = veorq_u8(vaesmcq_u8(vaeseq_u8(*st, vdupq_n_u8(0))),*key)}
}

fn aes_enc_last(st: &mut State, key: &State) {
    unsafe {*st = veorq_u8(vaeseq_u8(*st, vdupq_n_u8(0)),*key)}
}

fn aes_keygen_assist(next: &mut State, prev: &State, rcon: u8) {
    unsafe {
        let st = vaeseq_u8(*prev, vdupq_n_u8(0));
        let mut tmp = [0u8; 16];
        vst1q_u8(tmp.as_mut_ptr(), st);
        let tmp_new = [tmp[4], tmp[1], tmp[14], tmp[11],
                        tmp[1], tmp[14], tmp[11], tmp[4],
                        tmp[12], tmp[9], tmp[6], tmp[3],
                        tmp[9], tmp[6], tmp[3], tmp[12]];
        let st_new = vld1q_u8(tmp_new.as_ptr());
        let rcon_array = [0, rcon as u32, 0, rcon as u32];
        let rcon_vec = vreinterpretq_u8_u32(vld1q_u32(rcon_array.as_ptr()));
        *next = veorq_u8(st_new , rcon_vec);
    }
}

fn aes_keygen_assist0(next: &mut State, prev: &State, rcon: u8) {
    aes_keygen_assist(next, prev, rcon);
    unsafe {*next = vreinterpretq_u8_u32(vdupq_laneq_u32(vreinterpretq_u32_u8(*next), 3))}
}

fn aes_keygen_assist1(next: &mut State, prev: &State) {
    aes_keygen_assist(next, prev, 0);
    unsafe {*next = vreinterpretq_u8_u32(vdupq_laneq_u32(vreinterpretq_u32_u8(*next), 2))}
}


fn key_expansion_step(next: &mut State, prev: &State) {
    unsafe{
        let zero = vdupq_n_u32(0);
        let prev0 = vreinterpretq_u32_u8(*prev);
        let prev1 = veorq_u32(prev0, vextq_u32(zero, prev0, 3));
        let prev2 = veorq_u32(prev1, vextq_u32(zero, prev1, 3));
        let prev3 = veorq_u32(prev2, vextq_u32(zero, prev2, 3));
        *next = veorq_u8(*next,vreinterpretq_u8_u32(prev3));
    }
}

impl crate::platform::AESState for State {
    fn new() -> Self {
        new_state()
    }

    fn load_block(&mut self, b: &[u8]) {
        debug_assert!(b.len() == 16);
        unsafe {*self = vld1q_u8(b.as_ptr())};
    }

    fn store_block(&self, out: &mut [u8]) {
        debug_assert!(out.len() == 16);
        unsafe {vst1q_u8(out.as_mut_ptr(), *self)}
    }

    fn xor_block(&self, inp: &[u8], out: &mut [u8]) {
        debug_assert!(inp.len() == out.len() && inp.len() <= 16);
        let inp_vec = unsafe {vld1q_u8(inp.as_ptr()) };
        let out_vec = unsafe {veorq_u8(inp_vec, *self)};
        unsafe {vst1q_u8(out.as_mut_ptr(),out_vec)}
    }

    fn xor_key(&mut self, key: &Self) {
        xor_key1_state(self, key);
    }

    fn aes_enc(&mut self, key: &Self) {
        aes_enc(self, key);
        (self, key);
    }

    fn aes_enc_last(&mut self, key: &Self) {
        aes_enc_last(self, key);
    }

    fn aes_keygen_assist0<const RCON:i32>(&mut self, prev: &Self) {
        aes_keygen_assist0(self, prev, RCON as u8);
    }

    fn aes_keygen_assist1(&mut self, prev: &Self) {
        aes_keygen_assist1(self, prev);
    }

    fn key_expansion_step(&mut self, prev: &Self) {
        key_expansion_step(self, prev)
    }
}
