//! Obtain particular CPU features for AArch64 on Linux

use core::sync::atomic::{AtomicBool, Ordering};
use libc::{getauxval, AT_HWCAP, HWCAP_AES, HWCAP_PMULL, HWCAP_SHA2};

#[inline(always)]
fn auxval() {
    let val = unsafe { getauxval(AT_HWCAP) };
    let val_aes = val & HWCAP_AES != 0;
    AES.store(val_aes, Ordering::Relaxed);
    let val_pmull = val & HWCAP_PMULL != 0;
    PMULL.store(val_pmull, Ordering::Relaxed);
    let val_sha256 = val & HWCAP_SHA2 != 0;
    SHA256.store(val_sha256, Ordering::Relaxed);
}

static AES: AtomicBool = AtomicBool::new(false);
static PMULL: AtomicBool = AtomicBool::new(false);
static SHA256: AtomicBool = AtomicBool::new(false);

#[inline(always)]
pub(super) fn aes() -> bool {
    init();
    AES.load(Ordering::Relaxed)
}

#[inline(always)]
pub(super) fn pmull() -> bool {
    init();
    PMULL.load(Ordering::Relaxed)
}

#[inline(always)]
pub(super) fn sha256() -> bool {
    init();
    SHA256.load(Ordering::Relaxed)
}

static INITIALIZED: AtomicBool = AtomicBool::new(false);

/// Initialize CPU detection.
#[inline(always)]
pub(super) fn init() {
    if INITIALIZED.load(Ordering::Acquire) {
        return;
    }
    auxval();
    INITIALIZED.store(true, Ordering::Release);
}
