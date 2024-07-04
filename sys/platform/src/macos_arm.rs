//! Obtain particular CPU features for AArch64 on macOS

use libc::{c_char, c_void, sysctlbyname, uname, utsname};

#[allow(dead_code)]
fn cstr(src: &[i8]) -> &str {
    // default to length if no `0` present
    let end = src.iter().position(|&c| c == 0).unwrap_or(src.len());
    unsafe { core::str::from_utf8_unchecked(core::mem::transmute::<&[i8], &[u8]>(&src[0..end])) }
}

/// Check that we're actually on an ARM mac.
/// When this returns false, no other function in here must be called.
pub(crate) fn actually_arm() -> bool {
    let mut buf = utsname {
        sysname: [c_char::default(); 256],
        nodename: [c_char::default(); 256],
        release: [c_char::default(); 256],
        version: [c_char::default(); 256],
        machine: [c_char::default(); 256],
    };
    let error = unsafe { uname(&mut buf) };
    // buf.machine == "arm"
    // It could also be "arm64".
    let arm = buf.machine[0] == 97 && buf.machine[1] == 114 && buf.machine[2] == 109;
    error == 0 && arm
}

#[inline(always)]
fn check(feature: &[i8]) -> bool {
    let mut ret = 0i64;
    let mut size = core::mem::size_of::<i64>();
    let error = unsafe {
        sysctlbyname(
            feature.as_ptr(),
            &mut ret as *mut _ as *mut c_void,
            &mut size,
            core::ptr::null_mut(),
            0,
        )
    };
    error == 0 && ret > 0
}

#[inline(always)]
fn sysctl() {
    // Check that we're actually on arm and set everything to false if not.
    // This may happen when running on an intel mac.
    if !actually_arm() {
        return;
    }

    // hw.optional.AdvSIMD
    const ADV_SIMD_STR: [i8; 20] = [
        0x68, 0x77, 0x2e, 0x6f, 0x70, 0x74, 0x69, 0x6f, 0x6e, 0x61, 0x6c, 0x2e, 0x41, 0x64, 0x76,
        0x53, 0x49, 0x4d, 0x44, 0x00,
    ];
    if check(&ADV_SIMD_STR) {
        unsafe { ADV_SIMD = true };
    }

    // hw.optional.arm.FEAT_AES
    const FEAT_AES_STR: [i8; 25] = [
        0x68, 0x77, 0x2e, 0x6f, 0x70, 0x74, 0x69, 0x6f, 0x6e, 0x61, 0x6c, 0x2e, 0x61, 0x72, 0x6d,
        0x2e, 0x46, 0x45, 0x41, 0x54, 0x5f, 0x41, 0x45, 0x53, 0x00,
    ];
    if check(&FEAT_AES_STR) {
        unsafe { AES = true };
    }

    // hw.optional.arm.FEAT_PMULL
    const FEAT_PMULL_STR: [i8; 27] = [
        0x68, 0x77, 0x2e, 0x6f, 0x70, 0x74, 0x69, 0x6f, 0x6e, 0x61, 0x6c, 0x2e, 0x61, 0x72, 0x6d,
        0x2e, 0x46, 0x45, 0x41, 0x54, 0x5f, 0x50, 0x4d, 0x55, 0x4c, 0x4c, 0x00,
    ];
    if check(&FEAT_PMULL_STR) {
        unsafe { PMULL = true };
    }

    // hw.optional.arm.FEAT_SHA256
    const FEAT_SHA256_STR: [i8; 28] = [
        0x68, 0x77, 0x2e, 0x6f, 0x70, 0x74, 0x69, 0x6f, 0x6e, 0x61, 0x6c, 0x2e, 0x61, 0x72, 0x6d,
        0x2e, 0x46, 0x45, 0x41, 0x54, 0x5f, 0x53, 0x48, 0x41, 0x32, 0x35, 0x36, 0x00,
    ];
    if check(&FEAT_SHA256_STR) {
        unsafe { SHA256 = true };
    }
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
    // XXX[no_std]: no good way to do this in no_std
    // let _ = std::panic::catch_unwind(|| {
    // If there's no CPU ID because we're in SGX or whatever other reason,
    // we'll consider the hw detection as initialized but always return false.
    sysctl();
    // });
    unsafe {
        INITIALIZED = true;
    }
}
