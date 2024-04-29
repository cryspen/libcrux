use crate::{
    constants::FIELD_MODULUS,
    simd::{portable, simd_trait::*},
};

// TODO: Add target cfg guard here.
mod x64_avx2;
use x64_avx2::*;

#[derive(Clone, Copy)]
pub(crate) struct SIMD256Vector {
    elements: Vec,
}

impl Operations for SIMD256Vector {
    fn ZERO() -> Self {
        Self { elements: zero() }
    }

    fn to_i32_array(v: Self) -> [i32; 8] {
        store(v.elements)
    }

    fn from_i32_array(array: [i32; 8]) -> Self {
        Self {
            elements: load_vec(array),
        }
    }

    fn add_constant(v: Self, c: i32) -> Self {
        Self {
            elements: add(v.elements, load(c)),
        }
    }

    fn add(lhs: Self, rhs: &Self) -> Self {
        Self {
            elements: add(lhs.elements, rhs.elements),
        }
    }

    fn sub(lhs: Self, rhs: &Self) -> Self {
        Self {
            elements: sub(lhs.elements, rhs.elements),
        }
    }

    fn multiply_by_constant(v: Self, c: i32) -> Self {
        // In theory, we could get the wrong answer if the product occupies
        // more than 32 bits, but so far in the Kyber code that doesn't seem
        // to be the case.
        SIMD256Vector {
            elements: mul(v.elements, load(c)),
        }
    }

    fn bitwise_and_with_constant(v: Self, c: i32) -> Self {
        Self {
            elements: and(v.elements, load(c)),
        }
    }

    fn shift_right<const SHIFT_BY: i32>(v: Self) -> Self {
        Self {
            elements: shr::<SHIFT_BY>(v.elements),
        }
    }

    fn shift_left<const SHIFT_BY: i32>(v: Self) -> Self {
        Self {
            elements: shlli::<SHIFT_BY>(v.elements),
        }
    }

    fn cond_subtract_3329(v: Self) -> Self {
        let field_modulus = load(FIELD_MODULUS);
        let subtracted = sub(v.elements, field_modulus);
        let mask = and(shr::<31>(subtracted), field_modulus);

        Self {
            elements: add(subtracted, mask),
        }
    }

    fn barrett_reduce(v: Self) -> Self {
        let input = portable::PortableVector::from_i32_array(Self::to_i32_array(v));
        let output = portable::PortableVector::barrett_reduce(input);

        Self::from_i32_array(portable::PortableVector::to_i32_array(output))
    }

    fn montgomery_reduce(v: Self) -> Self {
        let input = portable::PortableVector::from_i32_array(Self::to_i32_array(v));
        let output = portable::PortableVector::montgomery_reduce(input);

        Self::from_i32_array(portable::PortableVector::to_i32_array(output))
    }

    fn compress_1(v: Self) -> Self {
        const FIELD_MODULUS_HAVLED: i32 = (FIELD_MODULUS - 1) / 2;
        const FIELD_MODULUS_QUARTERED: i32 = (FIELD_MODULUS - 1) / 4;

        let field_modulus_halved = load(FIELD_MODULUS_HAVLED);
        let field_modulus_quartered = load(FIELD_MODULUS_QUARTERED);

        let subtracted = sub(field_modulus_halved, v.elements);
        let mask = shr::<31>(subtracted);
        let value = shrli::<31>(sub(xor(mask, subtracted), field_modulus_quartered));
        Self { elements: value }
    }

    fn compress<const COEFFICIENT_BITS: i32>(v: Self) -> Self {
        let input = portable::PortableVector::from_i32_array(Self::to_i32_array(v));
        let output = portable::PortableVector::compress::<COEFFICIENT_BITS>(input);

        Self::from_i32_array(portable::PortableVector::to_i32_array(output))
    }

    fn ntt_layer_1_step(a: Self, zeta1: i32, zeta2: i32) -> Self {
        let input = portable::PortableVector::from_i32_array(Self::to_i32_array(a));
        let output = portable::PortableVector::ntt_layer_1_step(input, zeta1, zeta2);

        Self::from_i32_array(portable::PortableVector::to_i32_array(output))
    }

    fn ntt_layer_2_step(a: Self, zeta: i32) -> Self {
        let input = portable::PortableVector::from_i32_array(Self::to_i32_array(a));
        let output = portable::PortableVector::ntt_layer_2_step(input, zeta);

        Self::from_i32_array(portable::PortableVector::to_i32_array(output))
    }

    fn inv_ntt_layer_1_step(a: Self, zeta1: i32, zeta2: i32) -> Self {
        let input = portable::PortableVector::from_i32_array(Self::to_i32_array(a));
        let output = portable::PortableVector::inv_ntt_layer_1_step(input, zeta1, zeta2);

        Self::from_i32_array(portable::PortableVector::to_i32_array(output))
    }

    fn inv_ntt_layer_2_step(a: Self, zeta: i32) -> Self {
        let input = portable::PortableVector::from_i32_array(Self::to_i32_array(a));
        let output = portable::PortableVector::inv_ntt_layer_2_step(input, zeta);

        Self::from_i32_array(portable::PortableVector::to_i32_array(output))
    }

    fn ntt_multiply(lhs: &Self, rhs: &Self, zeta0: i32, zeta1: i32) -> Self {
        let input1 = portable::PortableVector::from_i32_array(SIMD256Vector::to_i32_array(*lhs));
        let input2 = portable::PortableVector::from_i32_array(SIMD256Vector::to_i32_array(*rhs));

        let output = portable::PortableVector::ntt_multiply(&input1, &input2, zeta0, zeta1);

        Self::from_i32_array(portable::PortableVector::to_i32_array(output))
    }

    fn serialize_1(a: Self) -> u8 {
        let v_bytes = store(a.elements);

        (v_bytes[0]
            | (v_bytes[1] << 1)
            | (v_bytes[2] << 2)
            | (v_bytes[3] << 3)
            | (v_bytes[4] << 4)
            | (v_bytes[5] << 5)
            | (v_bytes[6] << 6)
            | (v_bytes[7] << 7)) as u8
    }

    fn deserialize_1(a: u8) -> Self {
        let a = a as i32;
        let deserialized = load_i32s(
            (a >> 7) & 1,
            (a >> 6) & 1,
            (a >> 5) & 1,
            (a >> 4) & 1,
            (a >> 3) & 1,
            (a >> 2) & 1,
            (a >> 1) & 1,
            a & 1,
        );

        SIMD256Vector {
            elements: deserialized,
        }
    }

    fn serialize_4(a: Self) -> [u8; 4] {
        let shifts = load_i32s(0, 4, 0, 4, 0, 4, 0, 4);
        let shuffle_to = load_i8s(
            31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 12, 8, 4, 0, 15, 14, 13, 12, 11, 10, 9,
            8, 7, 6, 5, 4, 12, 8, 4, 0,
        );
        let value = shrli16::<4>(shuffle(shllv(a.elements, shifts), shuffle_to));

        [
            storei16::<0>(value) as u8,
            storei16::<1>(value) as u8,
            storei16::<8>(value) as u8,
            storei16::<9>(value) as u8,
        ]
    }

    fn deserialize_4(a: &[u8]) -> Self {
        let shifts = load_i32s(4, 0, 4, 0, 4, 0, 4, 0);
        let last_4_bits_mask = load(0xF);

        let deserialized = load_i32s(
            a[3] as i32,
            a[3] as i32,
            a[2] as i32,
            a[2] as i32,
            a[1] as i32,
            a[1] as i32,
            a[0] as i32,
            a[0] as i32,
        );
        let deserialized = and(shrllv(deserialized, shifts), last_4_bits_mask);

        SIMD256Vector {
            elements: deserialized,
        }
    }

    fn serialize_5(a: Self) -> [u8; 5] {
        let input = portable::PortableVector::from_i32_array(Self::to_i32_array(a));

        portable::PortableVector::serialize_5(input)
    }

    fn deserialize_5(a: &[u8]) -> Self {
        let output = portable::PortableVector::deserialize_5(a);

        Self::from_i32_array(portable::PortableVector::to_i32_array(output))
    }

    fn serialize_10(a: Self) -> [u8; 10] {
        let input = portable::PortableVector::from_i32_array(Self::to_i32_array(a));
        portable::PortableVector::serialize_10(input)
    }

    fn deserialize_10(a: &[u8]) -> Self {
        let output = portable::PortableVector::deserialize_10(a);

        Self::from_i32_array(portable::PortableVector::to_i32_array(output))
    }

    fn serialize_11(a: Self) -> [u8; 11] {
        let input = portable::PortableVector::from_i32_array(Self::to_i32_array(a));
        portable::PortableVector::serialize_11(input)
    }

    fn deserialize_11(a: &[u8]) -> Self {
        let output = portable::PortableVector::deserialize_11(a);

        Self::from_i32_array(portable::PortableVector::to_i32_array(output))
    }

    fn serialize_12(a: Self) -> [u8; 12] {
        let input = portable::PortableVector::from_i32_array(Self::to_i32_array(a));

        portable::PortableVector::serialize_12(input)
    }

    fn deserialize_12(a: &[u8]) -> Self {
        let output = portable::PortableVector::deserialize_12(a);

        Self::from_i32_array(portable::PortableVector::to_i32_array(output))
    }
}
