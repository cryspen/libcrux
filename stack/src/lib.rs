//! # Libcrux stack
//!
//! This is an internal crate that should not be used outside of libcrux.
//!
//! This crate implements a simple stack that allows re-using stack space
//! whenever possible and simple, mutable access.

#![no_std]

#[cfg(feature = "std")]
extern crate std;

/// The stack
pub struct Stack<const N: usize> {
    stack: [u8; N],
    pointer: core::cell::RefCell<usize>,
}

impl<const N: usize> Stack<N> {
    /// Create a new stack.
    pub fn alloc() -> Self {
        Self {
            stack: [0u8; N],
            pointer: 0.into(),
        }
    }

    /// Get an array of size L
    ///
    /// **PANICS** when requesting more than available.
    pub fn array(&self, len: usize) -> &mut [u8] {
        // This is unsafe and we should verify that it's correct.

        // Ensure we can get `len` bytes.
        assert!(*self.pointer.borrow() + len <= self.stack.len());

        // Getting the pointer is fine, but then adding the offset is unsafe
        let ptr = unsafe { self.stack.as_ptr().add(*self.pointer.borrow()) };

        // Here we force the const pointer to be mut
        let out = unsafe { std::slice::from_raw_parts_mut(ptr as *mut u8, len) };

        // Increment the pointer
        *self.pointer.borrow_mut() += len;

        out
    }

    /// Free the array on the stack.
    ///
    /// This is a dumb function. It can only free on the top (end)
    pub fn free(&self, array: &[u8]) {
        let array_ptr = unsafe { array.as_ptr().add(array.len()) };
        let stack_ptr = unsafe { self.stack.as_ptr().add(*self.pointer.borrow()) };

        assert!(array_ptr == stack_ptr);

        // Decrement the pointer
        *self.pointer.borrow_mut() -= array.len();

        // XXX: zeroize the values
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn paint(a: &mut [u8], b: u8) {
        for x in a {
            *x = b;
        }
    }

    #[test]
    fn create() {
        let stack = Stack::<64>::alloc();

        let first = stack.array(5);
        let second = stack.array(10);
        let third = stack.array(32);

        paint(first, 0x11);
        paint(second, 0x22);
        paint(third, 0x33);

        let last = stack.array(17);
        paint(last, 0x44);
        std::println!("stack: {:x?}", stack.stack);

        stack.free(last);
        let last_again = stack.array(16);
        paint(last_again, 0x55);

        std::println!("stack: {:x?}", stack.stack);
    }
}
