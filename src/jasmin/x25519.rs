// Allow dead code for now.
// The libjade code here isn't verified yet and thus isn't used.
#![allow(dead_code)]

use libjade_sys::{
    jade_scalarmult_curve25519_amd64_ref5, jade_scalarmult_curve25519_amd64_ref5_base,
};

type Point = [u8; 32];
type Scalar = [u8; 32];

pub(crate) fn derive(scalar: &Scalar, point: &Point) -> Result<Point, &'static str> {
    let mut result = Point::default();
    log::trace!("Jasmin x25519 ref");
    if unsafe {
        jade_scalarmult_curve25519_amd64_ref5(
            result.as_mut_ptr(),
            scalar.as_ptr() as _,
            point.as_ptr() as _,
        )
    } != 0
    {
        Err("Error while computing x25519.")
    } else {
        Ok(result)
    }
}

pub(crate) fn secret_to_public(scalar: &Scalar) -> Result<Point, &'static str> {
    log::trace!("Jasmin x25519 ref");
    let mut result = Point::default();
    if unsafe {
        jade_scalarmult_curve25519_amd64_ref5_base(result.as_mut_ptr(), scalar.as_ptr() as _)
    } != 0
    {
        Err("Error while computing x25519 base.")
    } else {
        Ok(result)
    }
}

/// This module requires mulx support, i.e. [`x25519_cpu_support`] needs to be
/// checked before calling into this module.
pub(crate) mod mulx {
    use libjade_sys::{
        jade_scalarmult_curve25519_amd64_mulx, jade_scalarmult_curve25519_amd64_mulx_base,
    };

    use super::{Point, Scalar};

    pub fn derive(scalar: &Scalar, point: &Point) -> Result<Point, &'static str> {
        log::trace!("Jasmin x25519 mulx");
        let mut result = Point::default();
        if unsafe {
            jade_scalarmult_curve25519_amd64_mulx(
                result.as_mut_ptr(),
                scalar.as_ptr() as _,
                point.as_ptr() as _,
            )
        } == 0
        {
            Ok(result)
        } else {
            Err("Error while computing x25519.")
        }
    }

    pub fn secret_to_public(scalar: &Scalar) -> Result<Point, &'static str> {
        log::trace!("Jasmin x25519 mulx");
        let mut result = Point::default();
        if unsafe {
            jade_scalarmult_curve25519_amd64_mulx_base(result.as_mut_ptr(), scalar.as_ptr() as _)
        } == 0
        {
            Ok(result)
        } else {
            Err("Error while computing x25519 base.")
        }
    }
}
