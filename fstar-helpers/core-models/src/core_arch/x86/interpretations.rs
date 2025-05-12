pub mod int_vec {
    //! Provides a machine integer vectors intepretation for AVX2 intrinsics.

    use crate::abstractions::{bitvec::int_vec_interp::*, funarr::FunArray};
    #[allow(unused)]
    use crate::core_arch::x86;

    pub fn _mm256_set1_epi32(x: i32) -> i32x8 {
        i32x8::from_fn(|_| x)
    }

    pub fn _mm256_mul_epi32(x: i32x8, y: i32x8) -> i64x4 {
        i64x4::from_fn(|i| (x[i * 2] as i64) * (y[i * 2] as i64))
    }
    pub fn _mm256_sub_epi32(x: i32x8, y: i32x8) -> i32x8 {
        i32x8::from_fn(|i| x[i].wrapping_sub(y[i]))
    }

    pub fn _mm256_shuffle_epi32<const CONTROL: i32>(x: i32x8) -> i32x8 {
        let indexes: FunArray<4, u64> = FunArray::from_fn(|i| ((CONTROL >> i * 2) % 4) as u64);
        i32x8::from_fn(|i| {
            if i < 4 {
                x[indexes[i]]
            } else {
                x[4 + indexes[i - 4]]
            }
        })
    }

    pub fn _mm256_blend_epi32<const CONTROL: i32>(x: i32x8, y: i32x8) -> i32x8 {
        FunArray::from_fn(|i| if (CONTROL >> i) % 2 == 0 { x[i] } else { y[i] })
    }

    pub use lemmas::flatten_circuit;
    // ! This module provides lemmas allowing to lift the intrinsics modeled in `super` from their version operating on AVX2 vectors to functions operating on machine integer vectors (e.g. on `i32x8`).
    pub mod lemmas {
        use super::*;

        #[allow(unused)]
        use crate::core_arch::x86 as upstream;
        #[allow(unused)]
        use crate::core_arch::x86::__m256i;

        /// An F* attribute that marks an item as being an lifting lemma.
        #[allow(dead_code)]
        #[hax_lib::fstar::before("irreducible")]
        pub const ETA_MATCH_EXPAND: () = ();

        #[hax_lib::fstar::before("[@@ $ETA_MATCH_EXPAND ]")]
        #[hax_lib::lemma]
        #[hax_lib::opaque]
        pub fn pointwise_i32x8(x: i32x8) -> Proof<{ hax_lib::eq(x, x.pointwise()) }> {}

        #[hax_lib::fstar::before("[@@ $ETA_MATCH_EXPAND ]")]
        #[hax_lib::lemma]
        #[hax_lib::opaque]
        pub fn pointwise_i64x4(x: i64x4) -> Proof<{ hax_lib::eq(x, x.pointwise()) }> {}

        /// An F* attribute that marks an item as being an lifting lemma.
        #[allow(dead_code)]
        #[hax_lib::fstar::before("irreducible")]
        pub const LIFT_LEMMA: () = ();

        /// Derives automatically a lift lemma for a given function
        macro_rules! mk_lift_lemma {
            ($name:ident$(<$(const $c:ident : $cty:ty),*>)?($($x:ident : $ty:ty),*) == $lhs:expr) => {
                #[hax_lib::opaque]
                #[hax_lib::lemma]
                #[hax_lib::fstar::before("[@@ $LIFT_LEMMA ]")]
                fn $name$(<$(const $c : $cty,)*>)?($($x : $ty,)*) -> Proof<{
                    hax_lib::eq(
                        unsafe {upstream::$name$(::<$($c,)*>)?($($x,)*)},
                        $lhs
                    )
                }> {}
            }
        }
        mk_lift_lemma!(
            _mm256_set1_epi32(x: i32) ==
            __m256i::from(super::_mm256_set1_epi32(x))
        );
        mk_lift_lemma!(
            _mm256_mul_epi32(x: __m256i, y: __m256i) ==
            __m256i::from(super::_mm256_mul_epi32(super::i32x8::from(x), super::i32x8::from(y)))
        );
        mk_lift_lemma!(
            _mm256_sub_epi32(x: __m256i, y: __m256i) ==
            __m256i::from(super::_mm256_sub_epi32(super::i32x8::from(x), super::i32x8::from(y)))
        );
        mk_lift_lemma!(
            _mm256_shuffle_epi32<const CONTROL: i32>(x: __m256i) ==
            __m256i::from(super::_mm256_shuffle_epi32::<CONTROL>(super::i32x8::from(x)))
        );
        mk_lift_lemma!(_mm256_blend_epi32<const CONTROL: i32>(x: __m256i, y: __m256i) ==
            __m256i::from(super::_mm256_blend_epi32::<CONTROL>(super::i32x8::from(x), super::i32x8::from(y)))
        );

        #[hax_lib::fstar::replace(
            r#"
        let ${flatten_circuit} (): FStar.Tactics.Tac unit =
            let open Tactics.Circuits in
            flatten_circuit
                [
                    "Core_models";
                    "FStar.FunctionalExtensionality";
                    `%Rust_primitives.cast_tc; `%Rust_primitives.unsize_tc;
                    "Core.Ops"; `%(.[]);
                ]
                (top_levels_of_attr (` $LIFT_LEMMA ))
                (top_levels_of_attr (` $SIMPLIFICATION_LEMMA ))
                (top_levels_of_attr (` $ETA_MATCH_EXPAND ))
        "#
        )]
        /// F* tactic: specialization of `Tactics.Circuits.flatten_circuit`.
        pub fn flatten_circuit() {}
    }

    #[cfg(all(test, any(target_arch = "x86", target_arch = "x86_64")))]
    mod tests {
        use crate::abstractions::bitvec::BitVec;
        use crate::core_arch::x86::upstream;

        /// Helper trait to generate random values
        pub trait HasRandom {
            fn random() -> Self;
        }

        impl HasRandom for i32 {
            fn random() -> Self {
                use rand::prelude::*;
                let mut rng = rand::rng();
                rng.random()
            }
        }

        impl<const N: u64> HasRandom for BitVec<N> {
            fn random() -> Self {
                BitVec::rand()
            }
        }

        /// Derives tests for a given intrinsics. Test that a given intrisics and its model compute the same thing over random values (1000 by default).
        macro_rules! mk {
            ($([$N:literal])?$name:ident$({$(<$($c:literal),*>),*})?($($x:ident : $ty:ident),*)) => {
                #[test]
                fn $name() {
                    #[allow(unused)]
                    const N: usize = {
                        let n: usize = 1000;
                        $(let n: usize = $N;)?
                        n
                    };
                    mk!(@[N]$name$($(<$($c),*>)*)?($($x : $ty),*));
                }
            };
            (@[$N:ident]$name:ident$(<$($c:literal),*>)?($($x:ident : $ty:ident),*)) => {
                for _ in 0..$N {
                    $(let $x = $ty::random();)*
                    assert_eq!(super::$name$(::<$($c,)*>)?($($x.into(),)*), unsafe {
                        BitVec::from(upstream::$name$(::<$($c,)*>)?($($x.into(),)*)).into()
                    });
                }
            };
            (@[$N:ident]$name:ident<$($c1:literal),*>$(<$($c:literal),*>)*($($x:ident : $ty:ident),*)) => {
                let one = || {
                    mk!(@[$N]$name<$($c1),*>($($x : $ty),*));
                };
                one();
                mk!(@[$N]$name$(<$($c),*>)*($($x : $ty),*));
            }
        }

        mk!(_mm256_set1_epi32(x: i32));
        mk!(_mm256_sub_epi32(x: BitVec, y: BitVec));
        mk!(_mm256_mul_epi32(x: BitVec, y: BitVec));
        mk!(_mm256_shuffle_epi32{<0b01_00_10_11>, <0b01_11_01_10>}(x: BitVec));
        mk!([100]_mm256_blend_epi32{<0>,<1>,<2>,<3>,<4>,<5>,<6>,<7>,<8>,<9>,<10>,<11>,<12>,<13>,<14>,<15>,<16>,<17>,<18>,<19>,<20>,<21>,<22>,<23>,<24>,<25>,<26>,<27>,<28>,<29>,<30>,<31>,<32>,<33>,<34>,<35>,<36>,<37>,<38>,<39>,<40>,<41>,<42>,<43>,<44>,<45>,<46>,<47>,<48>,<49>,<50>,<51>,<52>,<53>,<54>,<55>,<56>,<57>,<58>,<59>,<60>,<61>,<62>,<63>,<64>,<65>,<66>,<67>,<68>,<69>,<70>,<71>,<72>,<73>,<74>,<75>,<76>,<77>,<78>,<79>,<80>,<81>,<82>,<83>,<84>,<85>,<86>,<87>,<88>,<89>,<90>,<91>,<92>,<93>,<94>,<95>,<96>,<97>,<98>,<99>,<100>,<101>,<102>,<103>,<104>,<105>,<106>,<107>,<108>,<109>,<110>,<111>,<112>,<113>,<114>,<115>,<116>,<117>,<118>,<119>,<120>,<121>,<122>,<123>,<124>,<125>,<126>,<127>,<128>,<129>,<130>,<131>,<132>,<133>,<134>,<135>,<136>,<137>,<138>,<139>,<140>,<141>,<142>,<143>,<144>,<145>,<146>,<147>,<148>,<149>,<150>,<151>,<152>,<153>,<154>,<155>,<156>,<157>,<158>,<159>,<160>,<161>,<162>,<163>,<164>,<165>,<166>,<167>,<168>,<169>,<170>,<171>,<172>,<173>,<174>,<175>,<176>,<177>,<178>,<179>,<180>,<181>,<182>,<183>,<184>,<185>,<186>,<187>,<188>,<189>,<190>,<191>,<192>,<193>,<194>,<195>,<196>,<197>,<198>,<199>,<200>,<201>,<202>,<203>,<204>,<205>,<206>,<207>,<208>,<209>,<210>,<211>,<212>,<213>,<214>,<215>,<216>,<217>,<218>,<219>,<220>,<221>,<222>,<223>,<224>,<225>,<226>,<227>,<228>,<229>,<230>,<231>,<232>,<233>,<234>,<235>,<236>,<237>,<238>,<239>,<240>,<241>,<242>,<243>,<244>,<245>,<246>,<247>,<248>,<249>,<250>,<251>,<252>,<253>,<254>,<255>}(x: BitVec, y: BitVec));
    }
}
