use core::arch::x86_64::*;

pub(crate) type State = __m128i;

fn new_state() -> State {
    unsafe { _mm_setzero_si128() }
}

fn xor_key1_state(st: &mut State, k: &State) {
    unsafe { *st = _mm_xor_si128(*st, *k) }
}

fn aes_enc(st: &mut State, key: &State) {
    unsafe { *st = _mm_aesenc_si128(*st, *key) }
}

fn aes_enc_last(st: &mut State, key: &State) {
    unsafe { *st = _mm_aesenclast_si128(*st, *key) }
}

fn aes_keygen_assist<const RCON:i32>(next: &mut State, prev: &State) {
    unsafe { *next = _mm_aeskeygenassist_si128::<RCON>(*prev)}
}

fn aes_keygen_assist0<const RCON:i32>(next: &mut State, prev: &State) {
    aes_keygen_assist::<RCON>(next, prev);
    unsafe { *next = _mm_shuffle_epi32(*next, 0xff) }
}


fn aes_keygen_assist1(next: &mut State, prev: &State) {
    aes_keygen_assist::<0>(next, prev);
    unsafe { *next = _mm_shuffle_epi32(*next, 0xaa) }
}

fn key_expansion_step(next: &mut State, prev: &State) {
    unsafe{
        let p0 = _mm_xor_si128(*prev, _mm_slli_si128(*prev,4));
        let p1 = _mm_xor_si128(p0, _mm_slli_si128(p0,4));
        let p2 = _mm_xor_si128(p1, _mm_slli_si128(p1,4));
        *next = _mm_xor_si128(*next,p2);
    }
}


impl crate::platform::AESState for State {
    fn new() -> Self {
        new_state()
    }

    fn load_block(&mut self, b: &[u8]) {
        debug_assert!(b.len() == 16);
        unsafe { *self = _mm_loadu_si128(b.as_ptr() as *const __m128i) };
    }

    fn store_block(&self, out: &mut [u8]) {
        debug_assert!(out.len() == 16);
        unsafe { _mm_storeu_si128(out.as_mut_ptr() as *mut __m128i, *self) }
    }

    fn xor_block(&self, inp: &[u8], out: &mut [u8]) {
        debug_assert!(inp.len() == out.len() && inp.len() <= 16);
        let inp_vec = unsafe { _mm_loadu_si128(inp.as_ptr() as *const __m128i) };
        let out_vec = unsafe { _mm_xor_si128(inp_vec, *self) };
        unsafe { _mm_storeu_si128(out.as_mut_ptr() as *mut __m128i, out_vec) }
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
        aes_keygen_assist0::<RCON>(self, prev);
    }

    fn aes_keygen_assist1(&mut self, prev: &Self) {
        aes_keygen_assist1(self, prev);
    }

    fn key_expansion_step(&mut self, prev: &Self) {
        key_expansion_step(self, prev)
    }
}

#[test]
fn test() {
    unsafe {
        let x = _mm_set_epi32(3,2,1,0);
        let y = _mm_shuffle_epi32(x,0xaa);
        let w = _mm_slli_si128(x,4);
        let mut z:[i32; 4] = [0;4];
        _mm_storeu_si128(z.as_mut_ptr() as *mut __m128i, x);
        println!("{:?}",z);
        _mm_storeu_si128(z.as_mut_ptr() as *mut __m128i, w);
        println!("shift right 4 {:?}",z);
        _mm_storeu_si128(z.as_mut_ptr() as *mut __m128i, y);
        println!("shuffle aa {:?}",z);
    }
}