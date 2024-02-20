use libcrux::digest::shake128;
use rand::CryptoRng;

use rand;

use rand::RngCore;

pub(crate) struct FuzzRng {
    pub(crate) data: Vec<u8>,
}

impl FuzzRng {
    /// Create a new rng for fuzzing with 1024 bytes, using shake128.
    pub(crate) fn new(e: &[u8]) -> Self {
        let data: [u8; 1024] = shake128(e);
        Self {
            data: data.to_vec(),
        }
    }
}

impl RngCore for FuzzRng {
    fn next_u32(&mut self) -> u32 {
        let mut bytes: [u8; 4] = [0; 4];
        self.fill_bytes(&mut bytes);
        u32::from_be_bytes(bytes)
    }

    fn next_u64(&mut self) -> u64 {
        todo!()
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        dest.copy_from_slice(&self.data[0..dest.len()]);
        self.data = self.data.drain(dest.len()..).collect();
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand::Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}

impl CryptoRng for FuzzRng {}
