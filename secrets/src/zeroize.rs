//! Utilities for erasing memory

use crate::util::atomic_fence;

/// Zeroize the bytes in `mem`.
///
/// This is specialized for certain types for now.
#[inline(always)]
pub fn zeroize<T: Default + Clone + Copy>(mem: &mut [T]) {
    let len = mem.len();

    // Ensure len is not too big
    assert!(len <= isize::MAX as usize);

    // Get the default value to fill self with
    let default = T::default();

    // Take the raw pointer to this array
    let ptr = mem.as_mut_ptr();

    // Fill self with the default value
    //
    // This only works when
    // - self is a continuos arrays of elements of type `T` (u8)
    // - alignment of self must allow the volatile write
    for i in 0..len {
        unsafe { core::ptr::write_volatile(ptr.add(i), default) };
    }
    atomic_fence();
}
