module Libcrux_sha3.Generic_keccak
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_sha3.Traits in
  ()

(* item error backend: (RefMut) The mutation of this &mut is not allowed here.

Last available AST for this item:

#[inline(always)]
#[no_std()]
#[forbid(unsafe_code)]
#[feature(register_tool)]
#[register_tool(_hax)]
fn keccak<const N: int, T, const RATE: int, const DELIM: int, Anonymous: 'unk, Anonymous: 'unk>(
    data: [&[int]; N],
    out: [&mut [int]; N],
) -> tuple0
where
    _: libcrux_sha3::traits::t_KeccakItem<T, generic_value!(todo)>,
{
    rust_primitives::hax::dropped_body
}


Last AST:
/* print_rust: pitem: not implemented  (item: { Concrete_ident.T.def_id =
{ Concrete_ident.Imported.krate = "libcrux_sha3";
  path =
  [{ Concrete_ident.Imported.data =
     (Concrete_ident.Imported.TypeNs "generic_keccak"); disambiguator = 0 };
    { Concrete_ident.Imported.data =
      (Concrete_ident.Imported.ValueNs "keccak"); disambiguator = 0 }
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
fn squeeze_first_and_last<const N: int, T, const RATE: int, Anonymous: 'unk, Anonymous: 'unk>(
    s: &libcrux_sha3::generic_keccak::t_KeccakState<generic_value!(todo), T>,
    out: [&mut [int]; N],
) -> tuple0
where
    _: libcrux_sha3::traits::t_KeccakItem<T, generic_value!(todo)>,
{
    rust_primitives::hax::dropped_body
}


Last AST:
/* print_rust: pitem: not implemented  (item: { Concrete_ident.T.def_id =
{ Concrete_ident.Imported.krate = "libcrux_sha3";
  path =
  [{ Concrete_ident.Imported.data =
     (Concrete_ident.Imported.TypeNs "generic_keccak"); disambiguator = 0 };
    { Concrete_ident.Imported.data =
      (Concrete_ident.Imported.ValueNs "squeeze_first_and_last");
      disambiguator = 0 }
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
fn squeeze_first_block<const N: int, T, const RATE: int, Anonymous: 'unk, Anonymous: 'unk>(
    s: &libcrux_sha3::generic_keccak::t_KeccakState<generic_value!(todo), T>,
    out: [&mut [int]; N],
) -> tuple0
where
    _: libcrux_sha3::traits::t_KeccakItem<T, generic_value!(todo)>,
{
    rust_primitives::hax::dropped_body
}


Last AST:
/* print_rust: pitem: not implemented  (item: { Concrete_ident.T.def_id =
{ Concrete_ident.Imported.krate = "libcrux_sha3";
  path =
  [{ Concrete_ident.Imported.data =
     (Concrete_ident.Imported.TypeNs "generic_keccak"); disambiguator = 0 };
    { Concrete_ident.Imported.data =
      (Concrete_ident.Imported.ValueNs "squeeze_first_block");
      disambiguator = 0 }
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
fn squeeze_first_five_blocks<const N: int, T, const RATE: int, Anonymous: 'unk, Anonymous: 'unk>(
    mut s: libcrux_sha3::generic_keccak::t_KeccakState<generic_value!(todo), T>,
    out: [&mut [int]; N],
) -> tuple0
where
    _: libcrux_sha3::traits::t_KeccakItem<T, generic_value!(todo)>,
{
    {
        let hax_temp_output: tuple0 = { rust_primitives::hax::dropped_body };
        s
    }
}


Last AST:
/* print_rust: pitem: not implemented  (item: { Concrete_ident.T.def_id =
{ Concrete_ident.Imported.krate = "libcrux_sha3";
  path =
  [{ Concrete_ident.Imported.data =
     (Concrete_ident.Imported.TypeNs "generic_keccak"); disambiguator = 0 };
    { Concrete_ident.Imported.data =
      (Concrete_ident.Imported.ValueNs "squeeze_first_five_blocks");
      disambiguator = 0 }
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
fn squeeze_first_three_blocks<const N: int, T, const RATE: int, Anonymous: 'unk, Anonymous: 'unk>(
    mut s: libcrux_sha3::generic_keccak::t_KeccakState<generic_value!(todo), T>,
    out: [&mut [int]; N],
) -> tuple0
where
    _: libcrux_sha3::traits::t_KeccakItem<T, generic_value!(todo)>,
{
    {
        let hax_temp_output: tuple0 = { rust_primitives::hax::dropped_body };
        s
    }
}


Last AST:
/* print_rust: pitem: not implemented  (item: { Concrete_ident.T.def_id =
{ Concrete_ident.Imported.krate = "libcrux_sha3";
  path =
  [{ Concrete_ident.Imported.data =
     (Concrete_ident.Imported.TypeNs "generic_keccak"); disambiguator = 0 };
    { Concrete_ident.Imported.data =
      (Concrete_ident.Imported.ValueNs "squeeze_first_three_blocks");
      disambiguator = 0 }
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
fn squeeze_last<const N: int, T, const RATE: int, Anonymous: 'unk>(
    mut s: libcrux_sha3::generic_keccak::t_KeccakState<generic_value!(todo), T>,
    out: [&mut [int]; N],
) -> tuple0
where
    _: libcrux_sha3::traits::t_KeccakItem<T, generic_value!(todo)>,
{
    rust_primitives::hax::dropped_body
}


Last AST:
/* print_rust: pitem: not implemented  (item: { Concrete_ident.T.def_id =
{ Concrete_ident.Imported.krate = "libcrux_sha3";
  path =
  [{ Concrete_ident.Imported.data =
     (Concrete_ident.Imported.TypeNs "generic_keccak"); disambiguator = 0 };
    { Concrete_ident.Imported.data =
      (Concrete_ident.Imported.ValueNs "squeeze_last"); disambiguator = 0 }
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
fn squeeze_next_block<const N: int, T, const RATE: int, Anonymous: 'unk, Anonymous: 'unk>(
    mut s: libcrux_sha3::generic_keccak::t_KeccakState<generic_value!(todo), T>,
    out: [&mut [int]; N],
) -> tuple0
where
    _: libcrux_sha3::traits::t_KeccakItem<T, generic_value!(todo)>,
{
    {
        let hax_temp_output: tuple0 = { rust_primitives::hax::dropped_body };
        s
    }
}


Last AST:
/* print_rust: pitem: not implemented  (item: { Concrete_ident.T.def_id =
{ Concrete_ident.Imported.krate = "libcrux_sha3";
  path =
  [{ Concrete_ident.Imported.data =
     (Concrete_ident.Imported.TypeNs "generic_keccak"); disambiguator = 0 };
    { Concrete_ident.Imported.data =
      (Concrete_ident.Imported.ValueNs "squeeze_next_block");
      disambiguator = 0 }
    ]
  };
kind = Concrete_ident.Kind.Value }) */
 *)
