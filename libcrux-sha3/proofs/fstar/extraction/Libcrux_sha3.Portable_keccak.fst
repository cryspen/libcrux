module Libcrux_sha3.Portable_keccak
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v__vbcaxq_u64 (a b c: u64) : u64 = a ^. (b &. (~.c <: u64) <: u64)

let v__veor5q_u64 (a b c d e: u64) : u64 =
  let ab:u64 = a ^. b in
  let cd:u64 = c ^. d in
  let abcd:u64 = ab ^. cd in
  abcd ^. e

let v__veorq_n_u64 (a c: u64) : u64 = a ^. c

let slice_1_ (a: t_Array (t_Slice u8) (sz 1)) (start len: usize) : t_Array (t_Slice u8) (sz 1) =
  let list =
    [
      (a.[ sz 0 ] <: t_Slice u8).[ {
          Core.Ops.Range.f_start = start;
          Core.Ops.Range.f_end = start +! len <: usize
        }
        <:
        Core.Ops.Range.t_Range usize ]
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
  Rust_primitives.Hax.array_of_list 1 list

(* item error backend: 
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
    {
        let Tuple2(out00, out01): tuple2<&mut [int], &mut [int]> = {
            core::slice::impl__split_at_mut::<int>(
                &mut (deref(core::ops::index::Index::index(out, 0))),
                mid,
            )
        };
        {
            Tuple2([&mut (deref(out00))], [&mut (deref(out01))])
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
    { Concrete_ident.Imported.data =
      (Concrete_ident.Imported.ValueNs "split_at_mut_1"); disambiguator = 0
      }
    ]
  };
kind = Concrete_ident.Kind.Value }) */
 *)

let load_block
      (v_RATE: usize)
      (s: t_Array (t_Array u64 (sz 5)) (sz 5))
      (blocks: t_Array (t_Slice u8) (sz 1))
    : t_Array (t_Array u64 (sz 5)) (sz 5) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if
          ~.((v_RATE <=. (Core.Slice.impl__len #u8 (blocks.[ sz 0 ] <: t_Slice u8) <: usize) <: bool
            ) &&
            ((v_RATE %! sz 8 <: usize) =. sz 0 <: bool))
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: RATE <= blocks[0].len() && RATE % 8 == 0"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let s, hax_temp_output:t_Array (t_Array u64 (sz 5)) (sz 5) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = v_RATE /! sz 8 <: usize }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      s
      (fun s i ->
          let s:t_Array (t_Array u64 (sz 5)) (sz 5) = s in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
            (i /! sz 5 <: usize)
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s.[ i /! sz 5 <: usize ]
                  <:
                  t_Array u64 (sz 5))
                (i %! sz 5 <: usize)
                (((s.[ i /! sz 5 <: usize ] <: t_Array u64 (sz 5)).[ i %! sz 5 <: usize ] <: u64) ^.
                  (Core.Num.impl__u64__from_le_bytes (Core.Result.impl__unwrap #(t_Array u8 (sz 8))
                          #Core.Array.t_TryFromSliceError
                          (Core.Convert.f_try_into #(t_Slice u8)
                              #(t_Array u8 (sz 8))
                              ((blocks.[ sz 0 ] <: t_Slice u8).[ {
                                    Core.Ops.Range.f_start = sz 8 *! i <: usize;
                                    Core.Ops.Range.f_end = (sz 8 *! i <: usize) +! sz 8 <: usize
                                  }
                                  <:
                                  Core.Ops.Range.t_Range usize ]
                                <:
                                t_Slice u8)
                            <:
                            Core.Result.t_Result (t_Array u8 (sz 8)) Core.Array.t_TryFromSliceError)
                        <:
                        t_Array u8 (sz 8))
                    <:
                    u64)
                  <:
                  u64)
              <:
              t_Array u64 (sz 5))
          <:
          t_Array (t_Array u64 (sz 5)) (sz 5))
  in
  s

let rotate_left (v_LEFT v_RIGHT: i32) (x: u64) : u64 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.((v_LEFT +! v_RIGHT <: i32) =. 64l <: bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: LEFT + RIGHT == 64"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  (x <<! v_LEFT <: u64) |. (x >>! v_RIGHT <: u64)

let v__vrax1q_u64 (a b: u64) : u64 = a ^. (rotate_left 1l 63l b <: u64)

let v__vxarq_u64 (v_LEFT v_RIGHT: i32) (a b: u64) : u64 =
  let ab:u64 = a ^. b in
  rotate_left v_LEFT v_RIGHT ab

let load_block_full
      (v_RATE: usize)
      (s: t_Array (t_Array u64 (sz 5)) (sz 5))
      (blocks: t_Array (t_Array u8 (sz 200)) (sz 1))
    : t_Array (t_Array u64 (sz 5)) (sz 5) =
  let s:t_Array (t_Array u64 (sz 5)) (sz 5) =
    load_block v_RATE
      s
      (let list = [Rust_primitives.unsize (blocks.[ sz 0 ] <: t_Array u8 (sz 200)) <: t_Slice u8] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list)
  in
  s

(* item error backend: 
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
    {
        {
            for i in (core::iter::traits::collect::f_into_iter::<core::ops::range::t_Range<int>>(
                core::ops::range::Range {
                    f_start: 0,
                    f_end: core::ops::arith::Div::div(RATE, 8),
                },
            )) {
                core::slice::impl__copy_from_slice::<int>(
                    &mut (deref(core::ops::index::f_index_mut::<
                        [int],
                        core::ops::range::t_Range<int>,
                    >(
                        &mut (deref(core::ops::index::Index::index(out, 0))),
                        core::ops::range::Range {
                            f_start: core::ops::arith::Mul::mul(8, i),
                            f_end: core::ops::arith::Add::add(core::ops::arith::Mul::mul(8, i), 8),
                        },
                    ))),
                    rust_primitives::unsize(
                        &(core::num::impl__u64__to_le_bytes(core::ops::index::Index::index(
                            core::ops::index::Index::index(
                                deref(s),
                                core::ops::arith::Div::div(i, 5),
                            ),
                            core::ops::arith::Rem::rem(i, 5),
                        ))),
                    ),
                )
            }
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
    { Concrete_ident.Imported.data =
      (Concrete_ident.Imported.ValueNs "store_block"); disambiguator = 0 }
    ]
  };
kind = Concrete_ident.Kind.Value }) */
 *)

let store_block_full (v_RATE: usize) (s: t_Array (t_Array u64 (sz 5)) (sz 5))
    : t_Array (t_Array u8 (sz 200)) (sz 1) =
  let out:t_Array u8 (sz 200) = Rust_primitives.Hax.repeat 0uy (sz 200) in
  let _:Prims.unit =
    Rust_primitives.Hax.failure ""
      "libcrux_sha3::portable_keccak::store_block"
      v_RATE
      s
      (Rust_primitives.Hax.failure "" "[rust_primitives::unsize(&mut (deref(&mut (out))))]")
  in
  let list = [out] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
  Rust_primitives.Hax.array_of_list 1 list

(* item error backend: 
Last available AST for this item:

#[no_std()]
#[forbid(unsafe_code)]
#[feature(register_tool)]
#[register_tool(_hax)]
impl libcrux_sha3::traits::internal::t_KeccakItem<int, generic_value!(todo)> for int {
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
