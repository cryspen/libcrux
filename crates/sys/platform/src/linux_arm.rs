//! Obtain particular CPU features for AArch64 on Linux

use libc::{getauxval, AT_HWCAP, HWCAP_AES, HWCAP_ASIMD, HWCAP_PMULL, HWCAP_SHA2};

#[inline(always)]
fn auxval() {
    let val = unsafe { getauxval(AT_HWCAP) };
    let val_asimd = val & HWCAP_ASIMD != 0;
    unsafe { ADV_SIMD = val_asimd };
    let val_aes = val & HWCAP_AES != 0;
    unsafe { AES = val_aes };
    let val_pmull = val & HWCAP_PMULL != 0;
    unsafe { PMULL = val_pmull };
    let val_sha256 = val & HWCAP_SHA2 != 0;
    unsafe { SHA256 = val_sha256 };
}

static mut ADV_SIMD: bool = false;
static mut AES: bool = false;
static mut PMULL: bool = false;
static mut SHA256: bool = false;

#[inline(always)]
pub(super) fn aes() -> bool {
    init();
    unsafe { AES }
}

#[inline(always)]
pub(super) fn adv_simd() -> bool {
    init();
    unsafe { ADV_SIMD }
}

#[inline(always)]
pub(super) fn pmull() -> bool {
    init();
    unsafe { PMULL }
}

#[inline(always)]
pub(super) fn sha256() -> bool {
    init();
    unsafe { SHA256 }
}

static mut INITIALIZED: bool = false;

/// Initialize CPU detection.
#[inline(always)]
pub(super) fn init() {
    if unsafe { INITIALIZED } {
        return;
    }
    auxval();
    unsafe {
        INITIALIZED = true;
    }
}
