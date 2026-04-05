import Hax
import extraction.libcrux_intrinsics
import extraction.libcrux_sha3
import extraction.hacspec_sha3
import equivalence.Spec_Pure_Defs
import Std.Do.Triple
import Std.Tactic.Do

/-!
# SHA-3 implementation verification via mvcgen

Proves that the portable implementation (`N=1, T=u64`) of each Keccak-f step
matches the pure spec definitions in `Spec_Pure_Defs.lean`.
-/

open Std.Do
open libcrux_sha3.generic_keccak
open Spec.Pure

-- Sanity check: can we see both impl and spec
#check Impl_2.theta
#check theta_pure
