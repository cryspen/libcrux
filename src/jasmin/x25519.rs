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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::jasmin::testing::bytes_to_hex;

    fn bmi2_and_adx_are_supported() -> bool {
        std::arch::is_x86_feature_detected!("bmi2") && std::arch::is_x86_feature_detected!("adx")
    }

    #[test]
    fn test_derive() {
        let _ = pretty_env_logger::try_init();

        let public = [
            0x50, 0x4a, 0x36, 0x99, 0x9f, 0x48, 0x9c, 0xd2, 0xfd, 0xbc, 0x08, 0xba, 0xff, 0x3d,
            0x88, 0xfa, 0x00, 0x56, 0x9b, 0xa9, 0x86, 0xcb, 0xa2, 0x25, 0x48, 0xff, 0xde, 0x80,
            0xf9, 0x80, 0x68, 0x29,
        ];
        let private = [
            0xc8, 0xa9, 0xd5, 0xa9, 0x10, 0x91, 0xad, 0x85, 0x1c, 0x66, 0x8b, 0x07, 0x36, 0xc1,
            0xc9, 0xa0, 0x29, 0x36, 0xc0, 0xd3, 0xad, 0x62, 0x67, 0x08, 0x58, 0x08, 0x80, 0x47,
            0xba, 0x05, 0x74, 0x75,
        ];

        let shared = if bmi2_and_adx_are_supported() {
            mulx::derive(&private, &public).unwrap()
        } else {
            derive(&private, &public).unwrap()
        };

        println!("{:x?}", shared);
        let expected = "436a2c040cf45fea9b29a0cb81b1f41458f863d0d61b453d0a982720d6d61320";
        assert_eq!(expected, bytes_to_hex(&shared));
    }
}
