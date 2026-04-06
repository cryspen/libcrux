import Lake
open Lake DSL

package hacspec_sha3 where
  version := v!"0.1.0"

require Hax from git
  "https://github.com/cryspen/hax" @ "main" / "hax-lib" / "proof-libs" / "lean"

lean_lib Stubs where
  roots := #[`Stubs]

@[default_target]
lean_lib hacspec_sha3 where
  roots := #[`extraction.hacspec_sha3]

