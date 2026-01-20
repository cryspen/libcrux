// TODO: Implement proper memory zeroiation (#765). The hacl-rs code sometimes calls the memzero
// function, but unfortunately the memzero implementation that is extracted doesn't work well in
// Rust.
pub fn memzero<T: Copy>(_x: &mut [T], _len: u32) {
    /*
    let zero: T = unsafe { core::mem::zeroed() };
    for i in 0..len {
        x[i as usize] = zero;
    }
    */
}
