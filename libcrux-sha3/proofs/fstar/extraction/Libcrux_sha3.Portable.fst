module Libcrux_sha3.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

(* item error backend: (RefMut) The mutation of this &mut is not allowed here.

Last available AST for this item:

#[inline(always)]
#[no_std()]
#[forbid(unsafe_code)]
#[feature(register_tool)]
#[register_tool(_hax)]
fn keccakx1<const RATE: int, const DELIM: int, Anonymous: 'unk, Anonymous: 'unk>(
    data: [&[int]; 1],
    out: [&mut [int]; 1],
) -> tuple0 {
    rust_primitives::hax::dropped_body
}


Last AST:
/* print_rust: pitem: not implemented  (item: { Concrete_ident.T.def_id =
{ Concrete_ident.Imported.krate = "libcrux_sha3";
  path =
  [{ Concrete_ident.Imported.data =
     (Concrete_ident.Imported.TypeNs "portable"); disambiguator = 0 };
    { Concrete_ident.Imported.data =
      (Concrete_ident.Imported.ValueNs "keccakx1"); disambiguator = 0 }
    ]
  };
kind = Concrete_ident.Kind.Value }) */
 *)
