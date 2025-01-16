pub fn memzero<T: Copy>(x: &mut [T], len: u32) {
    let zero: T = unsafe { core::mem::zeroed() };
    for i in 0..len {
        x[i as usize] = zero;
    }
}
