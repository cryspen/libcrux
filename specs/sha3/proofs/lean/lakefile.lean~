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

lean_lib Spec_Pure where
  roots := #[`equivalence.Spec_Pure]

lean_lib Spec_Pure_Defs where
  roots := #[`equivalence.Spec_Pure_Defs]

lean_lib Spec_Pure_Mvcgen where
  roots := #[`equivalence.Spec_Pure_Mvcgen]

lean_lib Spec_Pure_Equality where
  roots := #[`equivalence.Spec_Pure_Equality]
