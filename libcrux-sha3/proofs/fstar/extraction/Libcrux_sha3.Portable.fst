module Libcrux_sha3.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

(* item error backend: 
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
    {
        libcrux_sha3::generic_keccak::keccak::<
            generic_value!(todo),
            int,
            generic_value!(todo),
            generic_value!(todo),
        >(data, out)
    }
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

/// A portable SHA3 224 implementation.
let sha224 (digest data: t_Slice u8) : t_Slice u8 =
  let _:Prims.unit =
    Rust_primitives.Hax.failure ""
      "libcrux_sha3::portable::keccakx1"
      (sz 144)
      6uy
      (let list = [data] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list)
      (Rust_primitives.Hax.failure "" "[&mut (digest)]")
  in
  digest

/// A portable SHA3 256 implementation.
let sha256 (digest data: t_Slice u8) : t_Slice u8 =
  let _:Prims.unit =
    Rust_primitives.Hax.failure ""
      "libcrux_sha3::portable::keccakx1"
      (sz 136)
      6uy
      (let list = [data] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list)
      (Rust_primitives.Hax.failure "" "[&mut (digest)]")
  in
  digest

/// A portable SHA3 384 implementation.
let sha384 (digest data: t_Slice u8) : t_Slice u8 =
  let _:Prims.unit =
    Rust_primitives.Hax.failure ""
      "libcrux_sha3::portable::keccakx1"
      (sz 104)
      6uy
      (let list = [data] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list)
      (Rust_primitives.Hax.failure "" "[&mut (digest)]")
  in
  digest

/// A portable SHA3 512 implementation.
let sha512 (digest data: t_Slice u8) : t_Slice u8 =
  let _:Prims.unit =
    Rust_primitives.Hax.failure ""
      "libcrux_sha3::portable::keccakx1"
      (sz 72)
      6uy
      (let list = [data] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list)
      (Rust_primitives.Hax.failure "" "[&mut (digest)]")
  in
  digest

/// A portable SHAKE128 implementation.
let shake128 (digest data: t_Slice u8) : t_Slice u8 =
  let _:Prims.unit =
    Rust_primitives.Hax.failure ""
      "libcrux_sha3::portable::keccakx1"
      (sz 168)
      31uy
      (let list = [data] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list)
      (Rust_primitives.Hax.failure "" "[&mut (digest)]")
  in
  digest

/// A portable SHAKE256 implementation.
let shake256 (digest data: t_Slice u8) : t_Slice u8 =
  let _:Prims.unit =
    Rust_primitives.Hax.failure ""
      "libcrux_sha3::portable::keccakx1"
      (sz 136)
      31uy
      (let list = [data] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list)
      (Rust_primitives.Hax.failure "" "[&mut (digest)]")
  in
  digest

type t_KeccakState1 = { f_state:Libcrux_sha3.Generic_keccak.t_KeccakState (sz 1) u64 }
