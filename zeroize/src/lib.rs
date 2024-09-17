pub trait Zeroize {
    fn zeroize(&mut self);
}

impl<T> Zeroize for T
where
    T: Default + Copy,
{
    fn zeroize(&mut self) {
        volatile_write(self, T::default());
        atomic_fence();
    }
}

impl<T> Zeroize for [T]
where
    T: Default + Copy,
{
    fn zeroize(&mut self) {
        assert!(self.len() <= isize::MAX as usize);

        // Safety:
        //
        // This is safe, because the slice is well aligned and is backed by a single allocated
        // object for at least `self.len()` elements of type `Z`.
        // `self.len()` is also not larger than an `isize`, because of the assertion above.
        // The memory of the slice should not wrap around the address space.
        unsafe { volatile_set(self.as_mut_ptr(), T::default(), self.len()) };
        atomic_fence();
    }
}

/// Prevent re-ordering
#[inline(always)]
fn atomic_fence() {
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
}

/// Perform a volatile write to the destination
#[inline(always)]
fn volatile_write<T: Copy + Sized>(dst: &mut T, src: T) {
    unsafe { core::ptr::write_volatile(dst, src) }
}

/// Perform a volatile `memset` operation which fills a slice with a value
///
/// Safety:
/// The memory pointed to by `dst` must be a single allocated object that is valid for `count`
/// contiguous elements of `T`.
/// `count` must not be larger than an `isize`.
/// `dst` being offset by `size_of::<T> * count` bytes must not wrap around the address space.
/// Also `dst` must be properly aligned.
#[inline(always)]
unsafe fn volatile_set<T: Copy + Sized>(dst: *mut T, src: T, count: usize) {
    for i in 0..count {
        // Safety:
        //
        // This is safe because there is room for at least `count` objects of type `T` in the
        // allocation pointed to by `dst`, because `count <= isize::MAX` and because
        // `dst.add(count)` must not wrap around the address space.
        let ptr = dst.add(i);

        // Safety:
        //
        // This is safe, because the pointer is valid and because `dst` is well aligned for `T` and
        // `ptr` is an offset of `dst` by a multiple of `size_of::<T>()` bytes.
        core::ptr::write_volatile(ptr, src);
    }
}

#[cfg(test)]
mod tests {
    use crate::Zeroize;

    #[test]
    fn array() {
        let mut x = [8u8; 987];
        x.zeroize();
        assert_eq!(x, [0u8; 987]);
    }

    #[test]
    fn slice() {
        let mut x = [8u8; 987];

        fn do_some(x: &mut [u8]) {
            x.zeroize();
        }
        do_some(&mut x);
        assert_eq!(x, [0u8; 987]);
    }
}
