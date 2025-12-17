//! Obtain particular CPU features for AArch64 on macOS

// See revision history for this file for how to check features on macOS.
// (For now, all features we're interested in are unconditionally available.)

#[inline(always)]
pub(super) fn aes() -> bool {
    // Apple Arm64 CPUs all support AES, even if they don't declare it.
    // https://github.com/RustCrypto/utils/issues/378#issuecomment-826985574
    true
}

#[inline(always)]
pub(super) fn pmull() -> bool {
    // Apple Arm64 CPUs all support PMULL, even if they don't declare it.
    // https://github.com/golang/go/issues/42747#issuecomment-732215259
    true
}

#[inline(always)]
pub(super) fn sha256() -> bool {
    // Apple Arm64 CPUs all support SHA-2, even if they don't declare it.
    // https://github.com/RustCrypto/utils/issues/378#issuecomment-826985574
    true
}
