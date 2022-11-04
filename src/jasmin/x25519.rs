use libjade::{jade_scalarmult_curve25519_amd64_mulx, jade_scalarmult_curve25519_amd64_ref5};

use crate::hw_detection::x25519_cpu_support;

type Curve25519Point = [u8; 32];
type Curve25519Scalar = [u8; 32];

pub fn x25519(scalar: &[u8], point: &[u8]) -> Result<Curve25519Point, &'static str> {
    let mut result = Curve25519Point::default();
    let r = if x25519_cpu_support() {
        log::trace!("Jasmin x25519 mulx");
        unsafe {
            jade_scalarmult_curve25519_amd64_mulx(
                result.as_mut_ptr(),
                scalar.as_ptr() as _,
                point.as_ptr() as _,
            )
        }
    } else {
        log::trace!("Jasmin x25519 ref");
        unsafe {
            jade_scalarmult_curve25519_amd64_ref5(
                result.as_mut_ptr(),
                scalar.as_ptr() as _,
                point.as_ptr() as _,
            )
        }
    };
    if r != 0 {
        Err("Error while computing x25519.")
    } else {
        Ok(result)
    }
}

pub fn x25519_base(scalar: &[u8]) -> Result<Curve25519Point, &'static str> {
    let mut result = Curve25519Point::default();
    let base = [
        0x09u8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00,
    ];

    let r = if x25519_cpu_support() {
        log::trace!("Jasmin x25519 mulx");
        unsafe {
            jade_scalarmult_curve25519_amd64_mulx(
                result.as_mut_ptr(),
                scalar.as_ptr() as _,
                base.as_ptr() as _,
            )
        }
    } else {
        log::trace!("Jasmin x25519 ref");
        unsafe {
            jade_scalarmult_curve25519_amd64_ref5(
                result.as_mut_ptr(),
                scalar.as_ptr() as _,
                base.as_ptr() as _,
            )
        }
    };
    if r != 0 {
        Err("Error while computing x25519.")
    } else {
        Ok(result)
    }
}
