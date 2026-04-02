import Lake
open Lake DSL

package libcrux_sha3 where
  version := v!"0.1.0"

require Hax from git
  "https://github.com/cryspen/hax" @ "main" / "hax-lib" / "proof-libs" / "lean"

lean_lib Stubs where
  roots := #[`Stubs]

lean_lib libcrux_intrinsics where
  roots := #[`extraction.libcrux_intrinsics]

@[default_target]
lean_lib libcrux_sha3 where
  roots := #[`extraction.libcrux_sha3]
