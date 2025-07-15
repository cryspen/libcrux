use crate::constants::{Eta, Gamma2, BITS_IN_LOWER_PART_OF_T};

// Each field element occupies 32 bits and the size of a simd_unit is 256 bits.
pub(crate) const COEFFICIENTS_IN_SIMD_UNIT: usize = 8;

// Note: For proofs, it is better to use concrete constants instead of const expressions
//COEFFICIENTS_IN_RING_ELEMENT / COEFFICIENTS_IN_SIMD_UNIT;
pub(crate) const SIMD_UNITS_IN_RING_ELEMENT: usize = 32;

pub const FIELD_MODULUS: i32 = 8_380_417;

// FIELD_MODULUS^{-1} mod MONTGOMERY_R
pub const INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u64 = 58_728_449;

/// If 'x' denotes a value of type `fe`, values having this type hold a
/// representative y ≡ x·MONTGOMERY_R (mod FIELD_MODULUS).
/// We use 'fer' as a shorthand for this type.
pub(crate) type FieldElementTimesMontgomeryR = i32;

#[cfg(not(eurydice))]
#[hax_lib::attributes]
pub(crate) trait Repr: Copy + Clone {
    #[requires(true)]
    fn repr(&self) -> [i32; COEFFICIENTS_IN_SIMD_UNIT];
}

pub mod specs {
    use hax_lib::*;

    pub(crate) const PRIME: u32 = 8380417;

    pub(crate) const MONT_R: u32 = 8380417;

    pub(crate) const FIELD_MAX: u32 = 8380416;

    pub(crate) const FIELD_MID: u32 = 4190208;

    pub(crate) const NTT_BASE_BOUND: u32 = FIELD_MID;

    const COEFFICIENTS_IN_SIMD_UNIT: usize = 8;

    type SIMDContent = [i32; COEFFICIENTS_IN_SIMD_UNIT];

    pub(crate) fn int_is_i32(i: Int) -> bool {
        i <= i32::MAX.to_int() && i >= i32::MIN.to_int()
    }

    #[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
    #[hax_lib::fstar::after(r#"
    let bounded_add_pre (a b: t_Array i32 (sz 8)) (b1:nat) (b2:nat):
        Lemma (requires (Spec.Utils.is_i32b_array_opaque b1 a /\ Spec.Utils.is_i32b_array_opaque b2 b /\ b1 + b2 <= 4294967295))
                (ensures (Libcrux_ml_dsa.Simd.Traits.Specs.add_pre a b))
               [SMTPat (Libcrux_ml_dsa.Simd.Traits.Specs.add_pre a b); 
                SMTPat (Spec.Utils.is_i32b_array_opaque b1 a);
                SMTPat (Spec.Utils.is_i32b_array_opaque b2 b)] = 
        reveal_opaque (`%$add_pre) ($add_pre)
    "#)]
    pub(crate) fn add_pre(lhs: &SIMDContent, rhs: &SIMDContent) -> Prop {
        forall(|i: usize| {
            implies(
                i < COEFFICIENTS_IN_SIMD_UNIT,
                int_is_i32(lhs[i].to_int() + rhs[i].to_int()),
            )
        })
    }

    #[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
    #[hax_lib::fstar::after(r#"
    let bounded_add_post (a b a_future: t_Array i32 (sz 8)) (b1 b2 b3:nat):
        Lemma (requires (Spec.Utils.is_i32b_array_opaque b1 a /\ Spec.Utils.is_i32b_array_opaque b2 b /\
                    b1 + b2 <= b3 /\ Libcrux_ml_dsa.Simd.Traits.Specs.add_post a b a_future))
            (ensures (Spec.Utils.is_i32b_array_opaque b3 a_future))
            [SMTPat (Libcrux_ml_dsa.Simd.Traits.Specs.add_post a b a_future); 
            SMTPat (Spec.Utils.is_i32b_array_opaque b1 a);
            SMTPat (Spec.Utils.is_i32b_array_opaque b2 b);
            SMTPat (Spec.Utils.is_i32b_array_opaque b3 a_future)] = 
        reveal_opaque (`%$add_post) ($add_post)
    "#)]
    pub(crate) fn add_post(lhs: &SIMDContent, rhs: &SIMDContent, future_lhs: &SIMDContent) -> Prop {
        forall(|i: usize| {
            implies(
                i < COEFFICIENTS_IN_SIMD_UNIT,
                future_lhs[i].to_int() == (lhs[i].to_int() + rhs[i].to_int()),
            )
        })
    }

    #[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
    #[hax_lib::fstar::after(r#"
    let bounded_sub_pre (a b: t_Array i32 (sz 8)) (b1:nat) (b2:nat):
        Lemma (requires (Spec.Utils.is_i32b_array_opaque b1 a /\ Spec.Utils.is_i32b_array_opaque b2 b /\ b1 + b2 <= 4294967295))
              (ensures (Libcrux_ml_dsa.Simd.Traits.Specs.sub_pre a b))
              [SMTPat (Libcrux_ml_dsa.Simd.Traits.Specs.sub_pre a b); 
               SMTPat (Spec.Utils.is_i32b_array_opaque b1 a);
               SMTPat (Spec.Utils.is_i32b_array_opaque b2 b)] = 
        reveal_opaque (`%$sub_pre) ($sub_pre)
    "#)]
    pub(crate) fn sub_pre(lhs: &SIMDContent, rhs: &SIMDContent) -> Prop {
        forall(|i: usize| {
            implies(
                i < COEFFICIENTS_IN_SIMD_UNIT,
                int_is_i32(lhs[i].to_int() - rhs[i].to_int()),
            )
        })
    }

    #[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
    #[hax_lib::fstar::after(r#"
    let bounded_sub_post (a b a_future: t_Array i32 (sz 8)) (b1 b2 b3:nat):
        Lemma (requires (Spec.Utils.is_i32b_array_opaque b1 a /\ Spec.Utils.is_i32b_array_opaque b2 b /\
                        b1 + b2 <= b3 /\ Libcrux_ml_dsa.Simd.Traits.Specs.sub_post a b a_future))
                (ensures (Spec.Utils.is_i32b_array_opaque b3 a_future))
                [SMTPat (Libcrux_ml_dsa.Simd.Traits.Specs.sub_post a b a_future); 
                SMTPat (Spec.Utils.is_i32b_array_opaque b1 a);
                SMTPat (Spec.Utils.is_i32b_array_opaque b2 b);
                SMTPat (Spec.Utils.is_i32b_array_opaque b3 a_future)] = 
                reveal_opaque (`%$sub_post) ($sub_post)
    "#)]
    pub(crate) fn sub_post(lhs: &SIMDContent, rhs: &SIMDContent, future_lhs: &SIMDContent) -> Prop {
        forall(|i: usize| {
            implies(
                i < COEFFICIENTS_IN_SIMD_UNIT,
                future_lhs[i].to_int() == (lhs[i].to_int() - rhs[i].to_int()),
            )
        })
    }
}


mod hey {
    pub use super::*;
    pub fn future<T>(x: T) -> T {
        panic!()
    }
    pub mod zero {
        use super::*;
        pub fn requires<T: Copy + Clone + Repr>() -> hax_lib::Prop {
            hax_lib::Prop::from(true)
        }
        pub fn ensures<T: Copy + Clone + Repr>(result: T) -> hax_lib::Prop {
            hax_lib::Prop::from(result.repr() == [0i32; COEFFICIENTS_IN_SIMD_UNIT])
        }
    }
    pub mod from_coefficient_array {
        use super::*;
        pub fn requires<T: Copy + Clone + Repr>(
            array: &[i32],
            out: &mut T,
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(array.len() == COEFFICIENTS_IN_SIMD_UNIT)
        }
        pub fn ensures<T: Copy + Clone + Repr>(
            array: &[i32],
            out: &mut T,
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(future(out).repr() == array)
        }
    }
    pub mod to_coefficient_array {
        use super::*;
        pub fn requires<T: Copy + Clone + Repr>(
            value: &T,
            out: &mut [i32],
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(out.len() == COEFFICIENTS_IN_SIMD_UNIT)
        }
        pub fn ensures<T: Copy + Clone + Repr>(
            value: &T,
            out: &mut [i32],
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(future(out) == value.repr())
        }
    }
    pub mod add {
        use super::*;
        pub fn requires<T: Copy + Clone + Repr>(lhs: &mut T, rhs: &T) -> hax_lib::Prop {
            hax_lib::Prop::from(specs::add_pre(&lhs.repr(), &rhs.repr()))
        }
        pub fn ensures<T: Copy + Clone + Repr>(lhs: &mut T, rhs: &T) -> hax_lib::Prop {
            hax_lib::Prop::from(
                specs::add_post(&lhs.repr(), &rhs.repr(), &future(lhs).repr()),
            )
        }
    }
    pub mod subtract {
        use super::*;
        pub fn requires<T: Copy + Clone + Repr>(lhs: &mut T, rhs: &T) -> hax_lib::Prop {
            hax_lib::Prop::from(specs::sub_pre(&lhs.repr(), &rhs.repr()))
        }
        pub fn ensures<T: Copy + Clone + Repr>(lhs: &mut T, rhs: &T) -> hax_lib::Prop {
            hax_lib::Prop::from(
                specs::sub_post(&lhs.repr(), &rhs.repr(), &future(lhs).repr()),
            )
        }
    }
    pub mod infinity_norm_exceeds {
        use super::*;
        pub fn requires<T: Copy + Clone + Repr>(
            simd_unit: &T,
            bound: i32,
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(
                hax_lib::fstar::prop!(
                    r#"v $bound > 0 /\ 
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (f_repr ${simd_unit})"#,
                ),
            )
        }
        pub fn ensures<T: Copy + Clone + Repr>(
            simd_unit: &T,
            bound: i32,
            _result: bool,
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(true)
        }
    }
    pub mod decompose {
        use super::*;
        pub fn requires<T: Copy + Clone + Repr>(
            gamma2: Gamma2,
            simd_unit: &T,
            low: &mut T,
            high: &mut T,
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(
                hax_lib::fstar::prop!(
                    r#"
        (v $gamma2 == v ${crate::constants::GAMMA2_V261_888} \/ 
         v $gamma2 == v ${crate::constants::GAMMA2_V95_232}) /\
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (f_repr ${simd_unit})"#,
                ),
            )
        }
        pub fn ensures<T: Copy + Clone + Repr>(
            gamma2: Gamma2,
            simd_unit: &T,
            low: &mut T,
            high: &mut T,
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(true)
        }
    }
    pub mod compute_hint {
        use super::*;
        pub fn requires<T: Copy + Clone + Repr>(
            low: &T,
            high: &T,
            gamma2: i32,
            hint: &mut T,
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(
                hax_lib::fstar::prop!(
                    r#"
        (v $gamma2 == v ${crate::constants::GAMMA2_V261_888} \/ 
         v $gamma2 == v ${crate::constants::GAMMA2_V95_232})"#,
                ),
            )
        }
        pub fn ensures<T: Copy + Clone + Repr>(
            low: &T,
            high: &T,
            gamma2: i32,
            hint: &mut T,
            result: usize,
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(result <= 8)
        }
    }
    pub mod use_hint {
        use super::*;
        pub fn requires<T: Copy + Clone + Repr>(
            gamma2: Gamma2,
            simd_unit: &T,
            hint: &mut T,
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(
                hax_lib::fstar::prop!(
                    r#"
        (v $gamma2 == v ${crate::constants::GAMMA2_V261_888} \/ 
         v $gamma2 == v ${crate::constants::GAMMA2_V95_232}) /\
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (f_repr ${simd_unit})"#,
                ),
            )
        }
        pub fn ensures<T: Copy + Clone + Repr>(
            gamma2: Gamma2,
            simd_unit: &T,
            hint: &mut T,
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(true)
        }
    }
    pub mod montgomery_multiply {
        use super::*;
        pub fn requires<T: Copy + Clone + Repr>(lhs: &mut T, rhs: &T) -> hax_lib::Prop {
            hax_lib::Prop::from(
                hax_lib::fstar::prop!(
                    r#"
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (${rhs.repr()})"#,
                ),
            )
        }
        pub fn ensures<T: Copy + Clone + Repr>(lhs: &mut T, rhs: &T) -> hax_lib::Prop {
            hax_lib::Prop::from(
                hax_lib::fstar::prop!(
                    r#"
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (f_repr ${lhs}_future) /\
        Spec.MLDSA.Math.(forall i. i < 8 ==> 
            mod_q (v (Seq.index (f_repr ${lhs}_future) i)) == 
            mod_q (v (Seq.index (${lhs.repr()}) i) * v (Seq.index (${rhs.repr()}) i) * 8265825))"#,
                ),
            )
        }
    }
    pub mod power2round {
        use super::*;
        pub fn requires<T: Copy + Clone + Repr>(
            t0: &mut T,
            t1: &mut T,
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(
                hax_lib::fstar::prop!(
                    r#"
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (f_repr ${t0})"#,
                ),
            )
        }
        pub fn ensures<T: Copy + Clone + Repr>(t0: &mut T, t1: &mut T) -> hax_lib::Prop {
            hax_lib::Prop::from(true)
        }
    }
    pub mod rejection_sample_less_than_field_modulus {
        use super::*;
        pub fn requires<T: Copy + Clone + Repr>(
            randomness: &[u8],
            out: &mut [i32],
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(true)
        }
        pub fn ensures<T: Copy + Clone + Repr>(
            randomness: &[u8],
            out: &mut [i32],
            _result: usize,
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(true)
        }
    }
    pub mod rejection_sample_less_than_eta_equals_2 {
        use super::*;
        pub fn requires<T: Copy + Clone + Repr>(
            randomness: &[u8],
            out: &mut [i32],
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(true)
        }
        pub fn ensures<T: Copy + Clone + Repr>(
            randomness: &[u8],
            out: &mut [i32],
            _result: usize,
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(true)
        }
    }
    pub mod rejection_sample_less_than_eta_equals_4 {
        use super::*;
        pub fn requires<T: Copy + Clone + Repr>(
            randomness: &[u8],
            out: &mut [i32],
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(true)
        }
        pub fn ensures<T: Copy + Clone + Repr>(
            randomness: &[u8],
            out: &mut [i32],
            _result: usize,
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(true)
        }
    }
    pub mod gamma1_serialize {
        use super::*;
        pub fn requires<T: Copy + Clone + Repr>(
            simd_unit: &T,
            serialized: &mut [u8],
            gamma1_exponent: usize,
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(
                match gamma1_exponent {
                    17 => serialized.len() == 18,
                    19 => serialized.len() == 20,
                    _ => false,
                },
            )
        }
        pub fn ensures<T: Copy + Clone + Repr>(
            simd_unit: &T,
            serialized: &mut [u8],
            gamma1_exponent: usize,
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(true)
        }
    }
    pub mod gamma1_deserialize {
        use super::*;
        pub fn requires<T: Copy + Clone + Repr>(
            serialized: &[u8],
            out: &mut T,
            gamma1_exponent: usize,
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(true)
        }
        pub fn ensures<T: Copy + Clone + Repr>(
            serialized: &[u8],
            out: &mut T,
            gamma1_exponent: usize,
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(true)
        }
    }
    pub mod commitment_serialize {
        use super::*;
        pub fn requires<T: Copy + Clone + Repr>(
            simd_unit: &T,
            serialized: &mut [u8],
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(serialized.len() == 4 || serialized.len() == 6)
        }
        pub fn ensures<T: Copy + Clone + Repr>(
            simd_unit: &T,
            serialized: &mut [u8],
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(future(&serialized).len() == serialized.len())
        }
    }
    pub mod error_serialize {
        use super::*;
        pub fn requires<T: Copy + Clone + Repr>(
            eta: Eta,
            simd_unit: &T,
            serialized: &mut [u8],
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(
                serialized.len()
                    == match eta {
                        Eta::Two => 3,
                        Eta::Four => 4,
                    },
            )
        }
        pub fn ensures<T: Copy + Clone + Repr>(
            eta: Eta,
            simd_unit: &T,
            serialized: &mut [u8],
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(true)
        }
    }
    pub mod error_deserialize {
        use super::*;
        pub fn requires<T: Copy + Clone + Repr>(
            eta: Eta,
            serialized: &[u8],
            out: &mut T,
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(
                serialized.len()
                    == match eta {
                        Eta::Two => 3,
                        Eta::Four => 4,
                    },
            )
        }
        pub fn ensures<T: Copy + Clone + Repr>(
            eta: Eta,
            serialized: &[u8],
            out: &mut T,
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(true)
        }
    }
    pub mod t0_serialize {
        use super::*;
        pub fn requires<T: Copy + Clone + Repr>(
            simd_unit: &T,
            out: &mut [u8],
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(
                hax_lib::fstar::prop!(
                    r#"forall i. let x = (pow2 (v $BITS_IN_LOWER_PART_OF_T - 1) - v (Seq.index (${simd_unit.repr()}) i)) in x >= 0 && x < pow2 13"#,
                ),
            )
        }
        pub fn ensures<T: Copy + Clone + Repr>(
            simd_unit: &T,
            out: &mut [u8],
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(true)
        }
    }
    pub mod t0_deserialize {
        use super::*;
        pub fn requires<T: Copy + Clone + Repr>(
            serialized: &[u8],
            out: &mut T,
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(serialized.len() == 13)
        }
        pub fn ensures<T: Copy + Clone + Repr>(
            serialized: &[u8],
            out: &mut T,
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(true)
        }
    }
    pub mod t1_serialize {
        use super::*;
        pub fn requires<T: Copy + Clone + Repr>(
            simd_unit: &T,
            out: &mut [u8],
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(out.len() == 10)
        }
        pub fn ensures<T: Copy + Clone + Repr>(
            simd_unit: &T,
            out: &mut [u8],
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(true)
        }
    }
    pub mod t1_deserialize {
        use super::*;
        pub fn requires<T: Copy + Clone + Repr>(
            serialized: &[u8],
            out: &mut T,
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(serialized.len() == 10)
        }
        pub fn ensures<T: Copy + Clone + Repr>(
            serialized: &[u8],
            out: &mut T,
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(true)
        }
    }
    pub mod ntt {
        use super::*;
        pub fn requires<T: Copy + Clone + Repr>(
            simd_units: &mut [T; SIMD_UNITS_IN_RING_ELEMENT],
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(
                hax_lib::fstar::prop!(
                    r#"
            (forall (i:nat). i < 32 ==> 
                Spec.Utils.is_i32b_array_opaque 
                (v ${specs::NTT_BASE_BOUND})
                (f_repr (Seq.index ${simd_units} i)))
        "#,
                ),
            )
        }
        pub fn ensures<T: Copy + Clone + Repr>(
            simd_units: &mut [T; SIMD_UNITS_IN_RING_ELEMENT],
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(
                hax_lib::fstar::prop!(
                    r#"
            (forall (i:nat). i < 32 ==> Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) 
                (f_repr (Seq.index ${simd_units}_future i)))
        "#,
                ),
            )
        }
    }
    pub mod invert_ntt_montgomery {
        use super::*;
        pub fn requires<T: Copy + Clone + Repr>(
            simd_units: &mut [T; SIMD_UNITS_IN_RING_ELEMENT],
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(
                hax_lib::fstar::prop!(
                    r#"
            (forall (i:nat). i < 32 ==> Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) 
                (f_repr (Seq.index ${simd_units} i)))
        "#,
                ),
            )
        }
        pub fn ensures<T: Copy + Clone + Repr>(
            simd_units: &mut [T; SIMD_UNITS_IN_RING_ELEMENT],
        ) -> hax_lib::Prop {
            hax_lib::Prop::from(
                hax_lib::fstar::prop!(
                    r#"
            (forall (i:nat). i < 32 ==> Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) 
                (f_repr (Seq.index ${simd_units}_future i)))
        "#,
                ),
            )
        }
    }
}


#[cfg(not(eurydice))]
#[hax_lib::attributes]
pub(crate) trait Operations: Copy + Clone + Repr {
    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| result.repr() == [0i32; COEFFICIENTS_IN_SIMD_UNIT])]
    fn zero() -> Self;

    #[hax_lib::requires(array.len() == COEFFICIENTS_IN_SIMD_UNIT)]
    #[hax_lib::ensures(|result| future(out).repr() == array)]
    fn from_coefficient_array(array: &[i32], out: &mut Self);

    #[hax_lib::requires(out.len() == COEFFICIENTS_IN_SIMD_UNIT)]
    #[hax_lib::ensures(|result| future(out) == value.repr())]
    fn to_coefficient_array(value: &Self, out: &mut [i32]);

    // Arithmetic
    #[hax_lib::requires(specs::add_pre(&lhs.repr(), &rhs.repr()))]
    #[hax_lib::ensures(|_| specs::add_post(&lhs.repr(), &rhs.repr(), &future(lhs).repr()))]
    fn add(lhs: &mut Self, rhs: &Self);

    #[hax_lib::requires(specs::sub_pre(&lhs.repr(), &rhs.repr()))]
    #[hax_lib::ensures(|_| specs::sub_post(&lhs.repr(), &rhs.repr(), &future(lhs).repr()))]
    fn subtract(lhs: &mut Self, rhs: &Self);

    #[hax_lib::requires(fstar!(r#"v $bound > 0 /\ 
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (f_repr ${simd_unit})"#))]
    fn infinity_norm_exceeds(simd_unit: &Self, bound: i32) -> bool;

    #[hax_lib::requires(fstar!(r#"
        (v $gamma2 == v ${crate::constants::GAMMA2_V261_888} \/ 
         v $gamma2 == v ${crate::constants::GAMMA2_V95_232}) /\
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (f_repr ${simd_unit})"#))]
    fn decompose(gamma2: Gamma2, simd_unit: &Self, low: &mut Self, high: &mut Self);

    #[hax_lib::requires(fstar!(r#"
        (v $gamma2 == v ${crate::constants::GAMMA2_V261_888} \/ 
         v $gamma2 == v ${crate::constants::GAMMA2_V95_232})"#))]
    #[hax_lib::ensures(|result| result <= 8)]
    fn compute_hint(low: &Self, high: &Self, gamma2: i32, hint: &mut Self) -> usize;

    #[hax_lib::requires(fstar!(r#"
        (v $gamma2 == v ${crate::constants::GAMMA2_V261_888} \/ 
         v $gamma2 == v ${crate::constants::GAMMA2_V95_232}) /\
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (f_repr ${simd_unit})"#))]
    fn use_hint(gamma2: Gamma2, simd_unit: &Self, hint: &mut Self);

    // Modular operations
    #[hax_lib::requires(fstar!(r#"
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (${rhs.repr()})"#))]
    #[hax_lib::ensures(|result| fstar!(r#"
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (f_repr ${lhs}_future) /\
        Spec.MLDSA.Math.(forall i. i < 8 ==> 
            mod_q (v (Seq.index (f_repr ${lhs}_future) i)) == 
            mod_q (v (Seq.index (${lhs.repr()}) i) * v (Seq.index (${rhs.repr()}) i) * 8265825))"#))]
    fn montgomery_multiply(lhs: &mut Self, rhs: &Self);

    // 261631 is the largest x such that x * pow2 13 <= 2143289343 (the barrett reduce input bound)
    #[hax_lib::requires(fstar!(r#"v $SHIFT_BY == 13 /\ 
        (forall i. i < 8 ==> v (Seq.index (f_repr ${simd_unit}) i) >= 0 /\
            v (Seq.index (f_repr ${simd_unit}) i) <= 261631)"#))]
    fn shift_left_then_reduce<const SHIFT_BY: i32>(simd_unit: &mut Self);

    // Decomposition operations
    #[hax_lib::requires(fstar!(r#"
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (f_repr ${t0})"#))]
    fn power2round(t0: &mut Self, t1: &mut Self);

    // Sampling
    //
    // In the sampling functions, since each SIMD unit can hold 8 coefficients,
    // we expect that `out` has the capacity for up to 8 coefficients.

    // Since each coefficient could potentially be sampled with 3 bytes, we expect
    // `randomness` to hold 24 bytes.
    #[hax_lib::requires(true)]
    fn rejection_sample_less_than_field_modulus(randomness: &[u8], out: &mut [i32]) -> usize;

    // Since each coefficient could potentially be sampled with half a byte,
    // we expect `randomness` to hold 4 bytes.
    #[hax_lib::requires(true)]
    fn rejection_sample_less_than_eta_equals_2(randomness: &[u8], out: &mut [i32]) -> usize;

    #[hax_lib::requires(true)]
    fn rejection_sample_less_than_eta_equals_4(randomness: &[u8], out: &mut [i32]) -> usize;

    // Encoding operations

    // Gamma1
    #[hax_lib::requires(match gamma1_exponent {
        17 => serialized.len() == 18,
        19 => serialized.len() == 20,
        _ => false,
    })]
    fn gamma1_serialize(simd_unit: &Self, serialized: &mut [u8], gamma1_exponent: usize);
    #[hax_lib::requires(true)]
    fn gamma1_deserialize(serialized: &[u8], out: &mut Self, gamma1_exponent: usize);

    // Commitment
    #[hax_lib::requires(serialized.len() == 4 || serialized.len() == 6)]
    #[hax_lib::ensures(|_| future(serialized).len() == serialized.len())]
    fn commitment_serialize(simd_unit: &Self, serialized: &mut [u8]);

    // Error
    #[hax_lib::requires(serialized.len() == match eta {
        Eta::Two => 3,
        Eta::Four => 4,
    })]
    fn error_serialize(eta: Eta, simd_unit: &Self, serialized: &mut [u8]);
    #[hax_lib::requires(serialized.len() == match eta {
        Eta::Two => 3,
        Eta::Four => 4,
    })]
    fn error_deserialize(eta: Eta, serialized: &[u8], out: &mut Self);

    // t0
    #[hax_lib::requires(fstar!(r#"forall i. let x = (pow2 (v $BITS_IN_LOWER_PART_OF_T - 1) - v (Seq.index (${simd_unit.repr()}) i)) in x >= 0 && x < pow2 13"#))]
    fn t0_serialize(simd_unit: &Self, out: &mut [u8]); // out len 13
    #[hax_lib::requires(serialized.len() == 13)]
    fn t0_deserialize(serialized: &[u8], out: &mut Self);

    // t1
    #[hax_lib::requires(out.len() == 10)]
    fn t1_serialize(simd_unit: &Self, out: &mut [u8]); // out len 10
    #[hax_lib::requires(serialized.len() == 10)]
    fn t1_deserialize(serialized: &[u8], out: &mut Self);

    // NTT
    #[hax_lib::requires(fstar!(r#"
        (forall (i:nat). i < 32 ==> 
            Spec.Utils.is_i32b_array_opaque 
            (v ${specs::NTT_BASE_BOUND})
            (f_repr (Seq.index ${simd_units} i)))
    "#))]
    #[hax_lib::ensures(|_| fstar!(r#"
        (forall (i:nat). i < 32 ==> Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) 
            (f_repr (Seq.index ${simd_units}_future i)))
    "#))]
    fn ntt(simd_units: &mut [Self; SIMD_UNITS_IN_RING_ELEMENT]);

    // invert NTT and convert to standard domain
    #[hax_lib::requires(fstar!(r#"
        (forall (i:nat). i < 32 ==> Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) 
            (f_repr (Seq.index ${simd_units} i)))
    "#))]
    #[hax_lib::ensures(|_| fstar!(r#"
        (forall (i:nat). i < 32 ==> Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) 
            (f_repr (Seq.index ${simd_units}_future i)))
    "#))]
    fn invert_ntt_montgomery(simd_units: &mut [Self; SIMD_UNITS_IN_RING_ELEMENT]);

    // Barrett reduce all coefficients
    fn reduce(simd_units: &mut [Self; SIMD_UNITS_IN_RING_ELEMENT]);
}

#[cfg(eurydice)]
pub(crate) trait Operations: Copy + Clone {
    fn zero() -> Self;

    fn from_coefficient_array(array: &[i32], out: &mut Self);
    fn to_coefficient_array(value: &Self, out: &mut [i32]);

    // Arithmetic
    fn add(lhs: &mut Self, rhs: &Self);
    fn subtract(lhs: &mut Self, rhs: &Self);
    fn infinity_norm_exceeds(simd_unit: &Self, bound: i32) -> bool;
    fn decompose(gamma2: Gamma2, simd_unit: &Self, low: &mut Self, high: &mut Self);
    fn compute_hint(low: &Self, high: &Self, gamma2: i32, hint: &mut Self) -> usize;
    fn use_hint(gamma2: Gamma2, simd_unit: &Self, hint: &mut Self);

    // Modular operations
    fn montgomery_multiply(lhs: &mut Self, rhs: &Self);
    fn shift_left_then_reduce<const SHIFT_BY: i32>(simd_unit: &mut Self);

    // Decomposition operations
    fn power2round(t0: &mut Self, t1: &mut Self);

    // Sampling
    //
    // In the sampling functions, since each SIMD unit can hold 8 coefficients,
    // we expect that `out` has the capacity for up to 8 coefficients.

    // Since each coefficient could potentially be sampled with 3 bytes, we expect
    // `randomness` to hold 24 bytes.
    fn rejection_sample_less_than_field_modulus(randomness: &[u8], out: &mut [i32]) -> usize;

    // Since each coefficient could potentially be sampled with half a byte,
    // we expect `randomness` to hold 4 bytes.
    fn rejection_sample_less_than_eta_equals_2(randomness: &[u8], out: &mut [i32]) -> usize;
    fn rejection_sample_less_than_eta_equals_4(randomness: &[u8], out: &mut [i32]) -> usize;

    // Encoding operations

    // Gamma1
    fn gamma1_serialize(simd_unit: &Self, serialized: &mut [u8], gamma1_exponent: usize);
    fn gamma1_deserialize(serialized: &[u8], out: &mut Self, gamma1_exponent: usize);

    // Commitment
    fn commitment_serialize(simd_unit: &Self, serialized: &mut [u8]);

    // Error
    fn error_serialize(eta: Eta, simd_unit: &Self, serialized: &mut [u8]);
    fn error_deserialize(eta: Eta, serialized: &[u8], out: &mut Self);

    // t0
    fn t0_serialize(simd_unit: &Self, out: &mut [u8]); // out len 13
    fn t0_deserialize(serialized: &[u8], out: &mut Self);

    // t1
    fn t1_serialize(simd_unit: &Self, out: &mut [u8]); // out len 10
    fn t1_deserialize(serialized: &[u8], out: &mut Self);

    // NTT
    fn ntt(simd_units: &mut [Self; SIMD_UNITS_IN_RING_ELEMENT]);

    // invert NTT and convert to standard domain
    fn invert_ntt_montgomery(simd_units: &mut [Self; SIMD_UNITS_IN_RING_ELEMENT]);

    // Barrett reduce all coefficients
    fn reduce(simd_units: &mut [Self; SIMD_UNITS_IN_RING_ELEMENT]);
}
