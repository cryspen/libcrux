module Libcrux_sha3.Portable_keccak
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val v__vbcaxq_u64 (a b c: u64) : Prims.Pure u64 Prims.l_True (fun _ -> Prims.l_True)

val v__veor5q_u64 (a b c d e: u64) : Prims.Pure u64 Prims.l_True (fun _ -> Prims.l_True)

val v__veorq_n_u64 (a c: u64) : Prims.Pure u64 Prims.l_True (fun _ -> Prims.l_True)

val v__vrax1q_u64 (a b: u64) : Prims.Pure u64 Prims.l_True (fun _ -> Prims.l_True)

val v__vxarq_u64 (v_LEFT v_RIGHT: i32) (a b: u64)
    : Prims.Pure u64 Prims.l_True (fun _ -> Prims.l_True)

val load_block
      (v_RATE: usize)
      (s: t_Array (t_Array u64 (sz 5)) (sz 5))
      (blocks: t_Array (t_Slice u8) (sz 1))
    : Prims.Pure (t_Array (t_Array u64 (sz 5)) (sz 5)) Prims.l_True (fun _ -> Prims.l_True)

val load_block_full
      (v_RATE: usize)
      (s: t_Array (t_Array u64 (sz 5)) (sz 5))
      (blocks: t_Array (t_Array u8 (sz 200)) (sz 1))
    : Prims.Pure (t_Array (t_Array u64 (sz 5)) (sz 5)) Prims.l_True (fun _ -> Prims.l_True)

val rotate_left (v_LEFT v_RIGHT: i32) (x: u64) : Prims.Pure u64 Prims.l_True (fun _ -> Prims.l_True)

val slice_1_ (a: t_Array (t_Slice u8) (sz 1)) (start len: usize)
    : Prims.Pure (t_Array (t_Slice u8) (sz 1)) Prims.l_True (fun _ -> Prims.l_True)

(* item error backend: (RefMut) The mutation of this &mut is not allowed here.

Last available AST for this item:

#[inline(always)]
#[no_std()]
#[forbid(unsafe_code)]
#[feature(register_tool)]
#[register_tool(_hax)]
fn split_at_mut_1_<Anonymous: 'unk>(
    out: [&mut [int]; 1],
    mid: int,
) -> tuple2<[&mut [int]; 1], [&mut [int]; 1]> {
    rust_primitives::hax::dropped_body
}


Last AST:
/* print_rust: pitem: not implemented  (item: { Concrete_ident.T.def_id =
{ Concrete_ident.Imported.krate = "libcrux_sha3";
  path =
  [{ Concrete_ident.Imported.data =
     (Concrete_ident.Imported.TypeNs "portable_keccak"); disambiguator = 0
     };
    { Concrete_ident.Imported.data =
      (Concrete_ident.Imported.ValueNs "split_at_mut_1"); disambiguator = 0
      }
    ]
  };
kind = Concrete_ident.Kind.Value }) */
 *)

(* item error backend: (RefMut) The mutation of this &mut is not allowed here.

Last available AST for this item:

#[inline(always)]
#[no_std()]
#[forbid(unsafe_code)]
#[feature(register_tool)]
#[register_tool(_hax)]
fn store_block<const RATE: int, Anonymous: 'unk, Anonymous: 'unk>(
    s: &[[int; 5]; 5],
    out: [&mut [int]; 1],
) -> tuple0 {
    rust_primitives::hax::dropped_body
}


Last AST:
/* print_rust: pitem: not implemented  (item: { Concrete_ident.T.def_id =
{ Concrete_ident.Imported.krate = "libcrux_sha3";
  path =
  [{ Concrete_ident.Imported.data =
     (Concrete_ident.Imported.TypeNs "portable_keccak"); disambiguator = 0
     };
    { Concrete_ident.Imported.data =
      (Concrete_ident.Imported.ValueNs "store_block"); disambiguator = 0 }
    ]
  };
kind = Concrete_ident.Kind.Value }) */
 *)

val store_block_full (v_RATE: usize) (s: t_Array (t_Array u64 (sz 5)) (sz 5))
    : Prims.Pure (t_Array (t_Array u8 (sz 200)) (sz 1)) Prims.l_True (fun _ -> Prims.l_True)

(* item error backend: (RefMut) The mutation of this &mut is not allowed here.

Last available AST for this item:

#[no_std()]
#[forbid(unsafe_code)]
#[feature(register_tool)]
#[register_tool(_hax)]
impl libcrux_sha3::traits::t_KeccakItem<int, generic_value!(todo)> for int {
    fn f_zero(_: tuple0) -> int {
        {
            0
        }
    }
    fn f_xor5(a: int, b: int, c: int, d: int, e: int) -> int {
        {
            libcrux_sha3::portable_keccak::v__veor5q_u64(a, b, c, d, e)
        }
    }
    fn f_rotate_left1_and_xor(a: int, b: int) -> int {
        {
            libcrux_sha3::portable_keccak::v__vrax1q_u64(a, b)
        }
    }
    fn f_xor_and_rotate<const LEFT: int, const RIGHT: int>(a: int, b: int) -> int {
        {
            libcrux_sha3::portable_keccak::v__vxarq_u64::<generic_value!(todo), generic_value!(todo)>(
                a, b,
            )
        }
    }
    fn f_and_not_xor(a: int, b: int, c: int) -> int {
        {
            libcrux_sha3::portable_keccak::v__vbcaxq_u64(a, b, c)
        }
    }
    fn f_xor_constant(a: int, c: int) -> int {
        {
            libcrux_sha3::portable_keccak::v__veorq_n_u64(a, c)
        }
    }
    fn f_xor(a: int, b: int) -> int {
        {
            core::ops::bit::BitXor::bitxor(a, b)
        }
    }
    fn f_load_block<const BLOCKSIZE: int, Anonymous: 'unk, Anonymous: 'unk>(
        mut a: [[int; 5]; 5],
        b: [&[int]; 1],
    ) -> tuple0 {
        {
            let hax_temp_output: tuple0 = {
                {
                    libcrux_sha3::portable_keccak::load_block::<generic_value!(todo)>(&mut (a), b)
                }
            };
            a
        }
    }
    fn f_store_block<const BLOCKSIZE: int, Anonymous: 'unk, Anonymous: 'unk>(
        a: &[[int; 5]; 5],
        b: [&mut [int]; 1],
    ) -> tuple0 {
        {
            libcrux_sha3::portable_keccak::store_block::<generic_value!(todo)>(&(deref(a)), b)
        }
    }
    fn f_load_block_full<const BLOCKSIZE: int, Anonymous: 'unk>(
        mut a: [[int; 5]; 5],
        b: [[int; 200]; 1],
    ) -> tuple0 {
        {
            let hax_temp_output: tuple0 = {
                {
                    libcrux_sha3::portable_keccak::load_block_full::<generic_value!(todo)>(
                        &mut (a),
                        b,
                    )
                }
            };
            a
        }
    }
    fn f_store_block_full<const BLOCKSIZE: int, Anonymous: 'unk>(
        a: &[[int; 5]; 5],
    ) -> [[int; 200]; 1] {
        {
            libcrux_sha3::portable_keccak::store_block_full::<generic_value!(todo)>(&(deref(a)))
        }
    }
    fn f_slice_n<Anonymous: 'unk>(a: [&[int]; 1], start: int, len: int) -> [&[int]; 1] {
        {
            libcrux_sha3::portable_keccak::slice_1_(a, start, len)
        }
    }
    fn f_split_at_mut_n<Anonymous: 'unk>(
        a: [&mut [int]; 1],
        mid: int,
    ) -> tuple2<[&mut [int]; 1], [&mut [int]; 1]> {
        {
            libcrux_sha3::portable_keccak::split_at_mut_1_(a, mid)
        }
    }
}


Last AST:
/* print_rust: pitem: not implemented  (item: { Concrete_ident.T.def_id =
{ Concrete_ident.Imported.krate = "libcrux_sha3";
  path =
  [{ Concrete_ident.Imported.data =
     (Concrete_ident.Imported.TypeNs "portable_keccak"); disambiguator = 0
     };
    { Concrete_ident.Imported.data = Concrete_ident.Imported.Impl;
      disambiguator = 0 }
    ]
  };
kind = Concrete_ident.Kind.Value }) */
 *)
