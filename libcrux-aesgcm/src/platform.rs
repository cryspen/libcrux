pub mod portable;

pub trait AESState: Copy {
    fn new() -> Self;
    fn load_block(&mut self, b: &[u8]);
    fn store_block(&self, out: &mut [u8]);
    fn xor_block(&self, inp: &[u8], out: &mut [u8]);

    fn xor_key(&mut self, key: &Self);
    fn aes_enc(&mut self, key: &Self);
    fn aes_enc_last(&mut self, key: &Self);
    fn aes_keygen_assist0(&mut self, prev: &Self, rcon: u8);
    fn aes_keygen_assist1(&mut self, prev: &Self);
    fn key_expansion_step(&mut self, prev: &Self);
}

pub trait GF128FieldElement: Copy {
    fn zero() -> Self;
    fn load_elem(b: &[u8]) -> Self;
    fn store_elem(&self, b: &mut [u8]);
    fn add(&mut self, other: &Self);
    fn mul(&mut self, other: &Self);
}
