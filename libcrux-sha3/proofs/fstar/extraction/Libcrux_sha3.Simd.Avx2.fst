module Libcrux_sha3.Simd.Avx2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

(* item error backend: (RefMut) The mutation of this &mut is not allowed here.

Last available AST for this item:

#[inline(always)]
#[cfg(feature = "simd256")]
#[no_std()]
#[forbid(unsafe_code)]
#[feature(register_tool)]
#[register_tool(_hax)]
fn split_at_mut_4_<Anonymous: 'unk>(
    out: [&mut [int]; 4],
    mid: int,
) -> tuple2<[&mut [int]; 4], [&mut [int]; 4]> {
    rust_primitives::hax::dropped_body
}


Last AST:
/* print_rust: pitem: not implemented  (item: { Concrete_ident.T.def_id =
{ Concrete_ident.Imported.krate = "libcrux_sha3";
  path =
  [{ Concrete_ident.Imported.data = (Concrete_ident.Imported.TypeNs "simd");
     disambiguator = 0 };
    { Concrete_ident.Imported.data =
      (Concrete_ident.Imported.TypeNs "avx2"); disambiguator = 0 };
    { Concrete_ident.Imported.data =
      (Concrete_ident.Imported.ValueNs "split_at_mut_4"); disambiguator = 0
      }
    ]
  };
kind = Concrete_ident.Kind.Value }) */
 *)

(* item error backend: (RefMut) The mutation of this &mut is not allowed here.

Last available AST for this item:

#[inline(always)]
#[cfg(feature = "simd256")]
#[no_std()]
#[forbid(unsafe_code)]
#[feature(register_tool)]
#[register_tool(_hax)]
fn store_block<const RATE: int, Anonymous: 'unk, Anonymous: 'unk>(
    s: &[[core::core_arch::x86::t____m256i; 5]; 5],
    out: [&mut [int]; 4],
) -> tuple0 {
    rust_primitives::hax::dropped_body
}


Last AST:
/* print_rust: pitem: not implemented  (item: { Concrete_ident.T.def_id =
{ Concrete_ident.Imported.krate = "libcrux_sha3";
  path =
  [{ Concrete_ident.Imported.data = (Concrete_ident.Imported.TypeNs "simd");
     disambiguator = 0 };
    { Concrete_ident.Imported.data =
      (Concrete_ident.Imported.TypeNs "avx2"); disambiguator = 0 };
    { Concrete_ident.Imported.data =
      (Concrete_ident.Imported.ValueNs "store_block"); disambiguator = 0 }
    ]
  };
kind = Concrete_ident.Kind.Value }) */
 *)

(* item error backend: (RefMut) The mutation of this &mut is not allowed here.

Last available AST for this item:

#[cfg(feature = "simd256")]
#[no_std()]
#[forbid(unsafe_code)]
#[feature(register_tool)]
#[register_tool(_hax)]
impl libcrux_sha3::traits::t_KeccakItem<core::core_arch::x86::t____m256i, generic_value!(todo)>
    for core::core_arch::x86::t____m256i
{
    fn f_zero(_: tuple0) -> core::core_arch::x86::t____m256i {
        {
            libcrux_intrinsics::avx2::mm256_set1_epi64x(0)
        }
    }
    fn f_xor5(
        a: core::core_arch::x86::t____m256i,
        b: core::core_arch::x86::t____m256i,
        c: core::core_arch::x86::t____m256i,
        d: core::core_arch::x86::t____m256i,
        e: core::core_arch::x86::t____m256i,
    ) -> core::core_arch::x86::t____m256i {
        {
            libcrux_sha3::simd::avx2::v__veor5q_u64(a, b, c, d, e)
        }
    }
    fn f_rotate_left1_and_xor(
        a: core::core_arch::x86::t____m256i,
        b: core::core_arch::x86::t____m256i,
    ) -> core::core_arch::x86::t____m256i {
        {
            libcrux_sha3::simd::avx2::v__vrax1q_u64(a, b)
        }
    }
    fn f_xor_and_rotate<const LEFT: int, const RIGHT: int>(
        a: core::core_arch::x86::t____m256i,
        b: core::core_arch::x86::t____m256i,
    ) -> core::core_arch::x86::t____m256i {
        {
            libcrux_sha3::simd::avx2::v__vxarq_u64::<generic_value!(todo), generic_value!(todo)>(
                a, b,
            )
        }
    }
    fn f_and_not_xor(
        a: core::core_arch::x86::t____m256i,
        b: core::core_arch::x86::t____m256i,
        c: core::core_arch::x86::t____m256i,
    ) -> core::core_arch::x86::t____m256i {
        {
            libcrux_sha3::simd::avx2::v__vbcaxq_u64(a, b, c)
        }
    }
    fn f_xor_constant(
        a: core::core_arch::x86::t____m256i,
        c: int,
    ) -> core::core_arch::x86::t____m256i {
        {
            libcrux_sha3::simd::avx2::v__veorq_n_u64(a, c)
        }
    }
    fn f_xor(
        a: core::core_arch::x86::t____m256i,
        b: core::core_arch::x86::t____m256i,
    ) -> core::core_arch::x86::t____m256i {
        {
            libcrux_intrinsics::avx2::mm256_xor_si256(a, b)
        }
    }
    fn f_load_block<const BLOCKSIZE: int, Anonymous: 'unk, Anonymous: 'unk>(
        mut a: [[core::core_arch::x86::t____m256i; 5]; 5],
        b: [&[int]; 4],
    ) -> tuple0 {
        {
            let hax_temp_output: tuple0 = {
                {
                    libcrux_sha3::simd::avx2::load_block::<generic_value!(todo)>(&mut (a), b)
                }
            };
            a
        }
    }
    fn f_store_block<const BLOCKSIZE: int, Anonymous: 'unk, Anonymous: 'unk>(
        a: &[[core::core_arch::x86::t____m256i; 5]; 5],
        b: [&mut [int]; 4],
    ) -> tuple0 {
        {
            libcrux_sha3::simd::avx2::store_block::<generic_value!(todo)>(&(deref(a)), b)
        }
    }
    fn f_load_block_full<const BLOCKSIZE: int, Anonymous: 'unk>(
        mut a: [[core::core_arch::x86::t____m256i; 5]; 5],
        b: [[int; 200]; 4],
    ) -> tuple0 {
        {
            let hax_temp_output: tuple0 = {
                {
                    libcrux_sha3::simd::avx2::load_block_full::<generic_value!(todo)>(&mut (a), b)
                }
            };
            a
        }
    }
    fn f_store_block_full<const BLOCKSIZE: int, Anonymous: 'unk>(
        a: &[[core::core_arch::x86::t____m256i; 5]; 5],
    ) -> [[int; 200]; 4] {
        {
            libcrux_sha3::simd::avx2::store_block_full::<generic_value!(todo)>(&(deref(a)))
        }
    }
    fn f_slice_n<Anonymous: 'unk>(a: [&[int]; 4], start: int, len: int) -> [&[int]; 4] {
        {
            libcrux_sha3::simd::avx2::slice_4_(a, start, len)
        }
    }
    fn f_split_at_mut_n<Anonymous: 'unk>(
        a: [&mut [int]; 4],
        mid: int,
    ) -> tuple2<[&mut [int]; 4], [&mut [int]; 4]> {
        {
            libcrux_sha3::simd::avx2::split_at_mut_4_(a, mid)
        }
    }
}


Last AST:
/* print_rust: pitem: not implemented  (item: { Concrete_ident.T.def_id =
{ Concrete_ident.Imported.krate = "libcrux_sha3";
  path =
  [{ Concrete_ident.Imported.data = (Concrete_ident.Imported.TypeNs "simd");
     disambiguator = 0 };
    { Concrete_ident.Imported.data =
      (Concrete_ident.Imported.TypeNs "avx2"); disambiguator = 0 };
    { Concrete_ident.Imported.data = Concrete_ident.Imported.Impl;
      disambiguator = 0 }
    ]
  };
kind = Concrete_ident.Kind.Value }) */
 *)
