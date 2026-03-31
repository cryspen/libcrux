module Hacspec_ml_dsa.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// Reduce a to [0, q-1].
let mod_q (a: i64) : i32 =
  let r:i32 = cast (a %! (cast (Hacspec_ml_dsa.Parameters.v_Q <: i32) <: i64) <: i64) <: i32 in
  if r <. mk_i32 0 then r +! Hacspec_ml_dsa.Parameters.v_Q else r

#push-options "--z3rlimit 150"

/// Centered modular reduction: returns r in [-(m/2), m/2).
let mod_pm (a m: i32) : Prims.Pure i32 (requires m >. mk_i32 0) (fun _ -> Prims.l_True) =
  let a64:i64 = cast (a <: i32) <: i64 in
  let m64:i64 = cast (m <: i32) <: i64 in
  let r:i64 = ((a64 %! m64 <: i64) +! m64 <: i64) %! m64 in
  let r:i32 = cast (r <: i64) <: i32 in
  if r >. (m /! mk_i32 2 <: i32) then r -! m else r

#pop-options

/// Power2Round(r) — FIPS 204, Algorithm 35.
/// Decomposes r into (r1, r0) such that r ≡ r1·2^d + r0 (mod q).
let power2round (r: i32)
    : Prims.Pure (i32 & i32)
      (requires r >=. mk_i32 0 && r <. Hacspec_ml_dsa.Parameters.v_Q)
      (fun _ -> Prims.l_True) =
  let r_plus:i32 = r %! Hacspec_ml_dsa.Parameters.v_Q in
  let r_plus:i32 = if r_plus <. mk_i32 0 then r_plus +! Hacspec_ml_dsa.Parameters.v_Q else r_plus in
  let two_d:i32 = mk_i32 1 <<! Hacspec_ml_dsa.Parameters.v_D in
  let r0:i32 = mod_pm r_plus two_d in
  let r1:i32 = (r_plus -! r0 <: i32) /! two_d in
  r1, r0 <: (i32 & i32)

#push-options "--z3rlimit 300"

/// Decompose(r) — FIPS 204, Algorithm 36.
/// Decomposes r into (r1, r0) such that r ≡ r1·(2·gamma2) + r0 (mod q).
/// Special case: when the straightforward rounding would give r1 = (q-1)/(2·gamma2),
/// returns (0, r0 - 1) instead.
let decompose (r gamma2: i32)
    : Prims.Pure (i32 & i32)
      (requires
        r >=. mk_i32 0 && r <. Hacspec_ml_dsa.Parameters.v_Q && gamma2 >. mk_i32 0 &&
        gamma2 <. (Hacspec_ml_dsa.Parameters.v_Q /! mk_i32 2 <: i32))
      (fun _ -> Prims.l_True) =
  let r_plus:i32 = r %! Hacspec_ml_dsa.Parameters.v_Q in
  let r_plus:i32 = if r_plus <. mk_i32 0 then r_plus +! Hacspec_ml_dsa.Parameters.v_Q else r_plus in
  let alpha:i32 = mk_i32 2 *! gamma2 in
  let r0:i32 = mod_pm r_plus alpha in
  if (r_plus -! r0 <: i32) =. (Hacspec_ml_dsa.Parameters.v_Q -! mk_i32 1 <: i32)
  then mk_i32 0, r0 -! mk_i32 1 <: (i32 & i32)
  else
    let r1:i32 = (r_plus -! r0 <: i32) /! alpha in
    r1, r0 <: (i32 & i32)

#pop-options

/// HighBits(r) — FIPS 204, Algorithm 37.
/// Returns r1 from Decompose(r).
let high_bits (r gamma2: i32)
    : Prims.Pure i32
      (requires
        r >=. mk_i32 0 && r <. Hacspec_ml_dsa.Parameters.v_Q && gamma2 >. mk_i32 0 &&
        gamma2 <. (Hacspec_ml_dsa.Parameters.v_Q /! mk_i32 2 <: i32))
      (fun _ -> Prims.l_True) = (decompose r gamma2)._1

/// LowBits(r) — FIPS 204, Algorithm 38.
/// Returns r0 from Decompose(r).
let low_bits (r gamma2: i32)
    : Prims.Pure i32
      (requires
        r >=. mk_i32 0 && r <. Hacspec_ml_dsa.Parameters.v_Q && gamma2 >. mk_i32 0 &&
        gamma2 <. (Hacspec_ml_dsa.Parameters.v_Q /! mk_i32 2 <: i32))
      (fun _ -> Prims.l_True) = (decompose r gamma2)._2

/// MakeHint(z, r) — FIPS 204, Algorithm 39.
/// Returns true if adding z to r changes the high bits.
let make_hint (z r gamma2: i32)
    : Prims.Pure bool
      (requires
        r >=. mk_i32 0 && r <. Hacspec_ml_dsa.Parameters.v_Q && gamma2 >. mk_i32 0 &&
        gamma2 <. (Hacspec_ml_dsa.Parameters.v_Q /! mk_i32 2 <: i32))
      (fun _ -> Prims.l_True) =
  let r1:i32 = high_bits r gamma2 in
  let v1:i32 =
    high_bits (mod_q ((cast (r <: i32) <: i64) +! (cast (z <: i32) <: i64) <: i64) <: i32) gamma2
  in
  r1 <>. v1

#push-options "--z3rlimit 300"

/// UseHint(h, r) — FIPS 204, Algorithm 40.
/// Returns the high bits of r, adjusted according to hint h.
let uuse_hint (hint: bool) (r gamma2: i32)
    : Prims.Pure i32
      (requires
        r >=. mk_i32 0 && r <. Hacspec_ml_dsa.Parameters.v_Q && gamma2 >. mk_i32 0 &&
        gamma2 <. (Hacspec_ml_dsa.Parameters.v_Q /! mk_i32 2 <: i32))
      (fun _ -> Prims.l_True) =
  let m:i32 = (Hacspec_ml_dsa.Parameters.v_Q -! mk_i32 1 <: i32) /! (mk_i32 2 *! gamma2 <: i32) in
  let (r1: i32), (r0: i32) = decompose r gamma2 in
  if hint && r0 >. mk_i32 0
  then (r1 +! mk_i32 1 <: i32) %! m
  else
    if hint && r0 <=. mk_i32 0 then (((r1 -! mk_i32 1 <: i32) %! m <: i32) +! m <: i32) %! m else r1

#pop-options

#push-options "--z3rlimit 150"

/// Infinity norm of a single coefficient (absolute value, centered).
let coeff_norm (a: i32) : i32 =
  let a_mod:i32 =
    cast ((((cast (a <: i32) <: i64) %! (cast (Hacspec_ml_dsa.Parameters.v_Q <: i32) <: i64) <: i64) +!
          (cast (Hacspec_ml_dsa.Parameters.v_Q <: i32) <: i64)
          <:
          i64) %!
        (cast (Hacspec_ml_dsa.Parameters.v_Q <: i32) <: i64)
        <:
        i64)
    <:
    i32
  in
  if a_mod >. (Hacspec_ml_dsa.Parameters.v_Q /! mk_i32 2 <: i32)
  then Hacspec_ml_dsa.Parameters.v_Q -! a_mod
  else a_mod

#pop-options
