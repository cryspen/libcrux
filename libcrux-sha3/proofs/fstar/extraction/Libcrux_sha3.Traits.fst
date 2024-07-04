module Libcrux_sha3.Traits
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

(* item error backend: (RefMut) The mutation of this &mut is not allowed here.

Last available AST for this item:

/** A trait for multiplexing implementations.*/
#[no_std()]
#[forbid(unsafe_code)]
#[feature(register_tool)]
#[register_tool(_hax)]
trait t_KeccakItem<Self_, const N: int>
where
    _: core::clone::t_Clone<Self>,
    _: core::marker::t_Copy<Self>,
{
    fn f_zero(_: tuple0) -> Self;
    fn f_xor5(_: Self, _: Self, _: Self, _: Self, _: Self) -> Self;
    fn f_rotate_left1_and_xor(_: Self, _: Self) -> Self;
    fn f_xor_and_rotate<const LEFT: int, const RIGHT: int>(_: Self, _: Self) -> Self;
    fn f_and_not_xor(_: Self, _: Self, _: Self) -> Self;
    fn f_xor_constant(_: Self, _: int) -> Self;
    fn f_xor(_: Self, _: Self) -> Self;
    fn f_load_block<const BLOCKSIZE: int, Anonymous: 'unk, Anonymous: 'unk>(
        _: [[Self; 5]; 5],
        _: [&[int]; N],
    ) -> [[Self; 5]; 5];
    fn f_store_block<const BLOCKSIZE: int, Anonymous: 'unk, Anonymous: 'unk>(
        _: &[[Self; 5]; 5],
        _: [&mut [int]; N],
    ) -> tuple0;
    fn f_load_block_full<const BLOCKSIZE: int, Anonymous: 'unk>(
        _: [[Self; 5]; 5],
        _: [[int; 200]; N],
    ) -> [[Self; 5]; 5];
    fn f_store_block_full<const BLOCKSIZE: int, Anonymous: 'unk>(
        _: &[[Self; 5]; 5],
    ) -> [[int; 200]; N];
    fn f_slice_n<Anonymous: 'unk>(_: [&[int]; N], _: int, _: int) -> [&[int]; N];
    fn f_split_at_mut_n<Anonymous: 'unk>(
        _: [&mut [int]; N],
        _: int,
    ) -> tuple2<[&mut [int]; N], [&mut [int]; N]>;
}


Last AST:
/* print_rust: pitem: not implemented  (item: { Concrete_ident.T.def_id =
{ Concrete_ident.Imported.krate = "libcrux_sha3";
  path =
  [{ Concrete_ident.Imported.data =
     (Concrete_ident.Imported.TypeNs "traits"); disambiguator = 0 };
    { Concrete_ident.Imported.data =
      (Concrete_ident.Imported.TypeNs "KeccakItem"); disambiguator = 0 }
    ]
  };
kind = Concrete_ident.Kind.Value }) */
 *)
