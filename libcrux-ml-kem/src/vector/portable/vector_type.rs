use core::fmt::Write;
use std::string::String;

use crate::vector::traits::FIELD_ELEMENTS_IN_VECTOR;

/// Values having this type hold a representative 'x' of the Kyber field.
/// We use 'fe' as a shorthand for this type.
pub(crate) type FieldElement = i16;

#[derive(Clone, Copy)]
pub struct PortableVector {
    pub(crate) elements: [FieldElement; FIELD_ELEMENTS_IN_VECTOR],
}

impl std::fmt::Debug for PortableVector {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut s = String::with_capacity(4 * FIELD_ELEMENTS_IN_VECTOR);
        for byte in self.elements {
            write!(s, "{:04X}", byte)?;
        }
        f.write_fmt(format_args!("{}", s))
    }
}

#[allow(non_snake_case)]
#[inline(always)]
pub fn zero() -> PortableVector {
    PortableVector {
        elements: [0i16; FIELD_ELEMENTS_IN_VECTOR],
    }
}

#[inline(always)]
pub fn from_i16_array(array: &[i16]) -> PortableVector {
    PortableVector {
        elements: array[0..16].try_into().unwrap(),
    }
}
