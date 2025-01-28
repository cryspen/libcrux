//! Utilities for secure crypto programming in Rust in libcrux.

/// Try to prevent re-ordering of instructions
#[inline(always)]
pub fn atomic_fence() {
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
}
