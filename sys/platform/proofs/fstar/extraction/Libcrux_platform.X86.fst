module Libcrux_platform.X86
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

(* item error backend: (reject_Unsafe) ExplicitRejection { reason: "a node of kind [Unsafe] have been found in the AST" }
Last available AST for this item:

#[inline(never)]
#[inline(always)]
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
#[allow(non_upper_case_globals)]
#[no_std()]
#[feature(register_tool)]
#[register_tool(_hax)]
unsafe fn init__cpuid(leaf: int) -> core::core_arch::x86::cpuid::t_CpuidResult {
    rust_primitives::hax::dropped_body
}


Last AST:
/** print_rust: pitem: not implemented  (item: { Concrete_ident.T.def_id =
  { Concrete_ident.Imported.krate = "libcrux_platform";
    path =
    [{ Concrete_ident.Imported.data = (Concrete_ident.Imported.TypeNs "x86");
       disambiguator = 0 };
      { Concrete_ident.Imported.data =
        (Concrete_ident.Imported.ValueNs "init"); disambiguator = 0 };
      { Concrete_ident.Imported.data =
        (Concrete_ident.Imported.ValueNs "cpuid"); disambiguator = 0 }
      ]
    };
  kind = Concrete_ident.Kind.Value }) */
const _: () = ();
 *)

(* item error backend: (reject_Unsafe) ExplicitRejection { reason: "a node of kind [Unsafe] have been found in the AST" }
Last available AST for this item:

#[inline(never)]
#[inline(always)]
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
#[allow(non_upper_case_globals)]
#[no_std()]
#[feature(register_tool)]
#[register_tool(_hax)]
unsafe fn init__cpuid_count(
    leaf: int,
    sub_leaf: int,
) -> core::core_arch::x86::cpuid::t_CpuidResult {
    rust_primitives::hax::dropped_body
}


Last AST:
/** print_rust: pitem: not implemented  (item: { Concrete_ident.T.def_id =
  { Concrete_ident.Imported.krate = "libcrux_platform";
    path =
    [{ Concrete_ident.Imported.data = (Concrete_ident.Imported.TypeNs "x86");
       disambiguator = 0 };
      { Concrete_ident.Imported.data =
        (Concrete_ident.Imported.ValueNs "init"); disambiguator = 0 };
      { Concrete_ident.Imported.data =
        (Concrete_ident.Imported.ValueNs "cpuid_count"); disambiguator = 0 }
      ]
    };
  kind = Concrete_ident.Kind.Value }) */
const _: () = ();
 *)
