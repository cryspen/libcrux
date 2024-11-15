//! # Libcrux stack
//!
//! This is an internal crate that should not be used outside of libcrux.
//!
//! This crate implements a simple stack that allows re-using stack space
//! whenever possible and simple, mutable access.

#![no_std]

/// The stack
pub struct Stack<const N: usize> {
    stack: [u8; N],
    pointer: usize,
}

impl<const N: usize> Stack<N> {
    fn alloc() -> Self {
        Self {
            stack: [0u8; N],
            pointer: 0,
        }
    }

    /// Get an array of size L
    fn array<const L: usize>()

    fn free(self) {}
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn create() {}
}
