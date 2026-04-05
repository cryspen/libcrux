import Lake
open Lake DSL

package libcrux_sha3 where
  version := v!"0.1.0"

require Hax from git
  "https://github.com/cryspen/hax" @ "main" / "hax-lib" / "proof-libs" / "lean"

require hacspec_sha3 from "../../../../../specs/sha3/proofs/lean"

lean_lib LibcruxStubs where
  roots := #[`LibcruxStubs]

lean_lib libcrux_intrinsics where
  roots := #[`extraction.libcrux_intrinsics]

lean_lib libcrux_sha3 where
  roots := #[`extraction.libcrux_sha3]

@[default_target]
lean_lib Impl_Spec_Mvcgen where
  roots := #[`Impl_Spec_Mvcgen]
