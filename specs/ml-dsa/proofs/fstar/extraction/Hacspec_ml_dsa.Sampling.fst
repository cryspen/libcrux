module Hacspec_ml_dsa.Sampling
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// Concatenate a 32-byte seed with two single bytes → [u8; 34].
let concat_2bytes (a: t_Array u8 (mk_usize 32)) (b c: u8) : t_Array u8 (mk_usize 34) =
  let result:t_Array u8 (mk_usize 34) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 34) in
  let result:t_Array u8 (mk_usize 34) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_to result
      ({ Core_models.Ops.Range.f_end = mk_usize 32 } <: Core_models.Ops.Range.t_RangeTo usize)
      (Core_models.Slice.impl__copy_from_slice #u8
          (result.[ { Core_models.Ops.Range.f_end = mk_usize 32 }
              <:
              Core_models.Ops.Range.t_RangeTo usize ]
            <:
            t_Slice u8)
          (a <: t_Slice u8)
        <:
        t_Slice u8)
  in
  let result:t_Array u8 (mk_usize 34) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (mk_usize 32) b
  in
  let result:t_Array u8 (mk_usize 34) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result (mk_usize 33) c
  in
  result

/// Concatenate a 64-byte seed with a u16 in little-endian → [u8; 66].
let concat_u16_le (a: t_Array u8 (mk_usize 64)) (v_val: u16) : t_Array u8 (mk_usize 66) =
  let result:t_Array u8 (mk_usize 66) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 66) in
  let result:t_Array u8 (mk_usize 66) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_to result
      ({ Core_models.Ops.Range.f_end = mk_usize 64 } <: Core_models.Ops.Range.t_RangeTo usize)
      (Core_models.Slice.impl__copy_from_slice #u8
          (result.[ { Core_models.Ops.Range.f_end = mk_usize 64 }
              <:
              Core_models.Ops.Range.t_RangeTo usize ]
            <:
            t_Slice u8)
          (a <: t_Slice u8)
        <:
        t_Slice u8)
  in
  let result:t_Array u8 (mk_usize 66) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (mk_usize 64)
      (cast (v_val <: u16) <: u8)
  in
  let result:t_Array u8 (mk_usize 66) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (mk_usize 65)
      (cast (v_val >>! mk_i32 8 <: u16) <: u8)
  in
  result

#push-options "--z3rlimit 300"

#push-options "--admit_smt_queries true"

/// SampleInBall(ρ) — FIPS 204, Algorithm 29.
/// Samples a polynomial c ∈ R with coefficients in {-1, 0, 1}
/// and Hamming weight exactly τ, using a Fisher-Yates shuffle.
let sample_in_ball (rho: t_Slice u8) (tau: usize)
    : Prims.Pure (t_Array i32 (mk_usize 256))
      (requires tau <=. mk_usize 256)
      (fun _ -> Prims.l_True) =
  let (buf: t_Array u8 (mk_usize 1024)):t_Array u8 (mk_usize 1024) =
    Hacspec_ml_dsa.Hash_functions.h (mk_usize 1024) rho
  in
  let c:t_Array i32 (mk_usize 256) = Hacspec_ml_dsa.Parameters.v_ZERO_POLY in
  let signs:u64 =
    Core_models.Num.impl_u64__from_le_bytes (let list =
          [
            buf.[ mk_usize 0 ] <: u8;
            buf.[ mk_usize 1 ] <: u8;
            buf.[ mk_usize 2 ] <: u8;
            buf.[ mk_usize 3 ] <: u8;
            buf.[ mk_usize 4 ] <: u8;
            buf.[ mk_usize 5 ] <: u8;
            buf.[ mk_usize 6 ] <: u8;
            buf.[ mk_usize 7 ] <: u8
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
        Rust_primitives.Hax.array_of_list 8 list)
  in
  let byte_offset:usize = mk_usize 8 in
  let (byte_offset: usize), (c: t_Array i32 (mk_usize 256)) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      tau
      (fun temp_0_ temp_1_ ->
          let (byte_offset: usize), (c: t_Array i32 (mk_usize 256)) = temp_0_ in
          let _:usize = temp_1_ in
          true)
      (byte_offset, c <: (usize & t_Array i32 (mk_usize 256)))
      (fun temp_0_ counter ->
          let (byte_offset: usize), (c: t_Array i32 (mk_usize 256)) = temp_0_ in
          let counter:usize = counter in
          let i:usize = (mk_usize 256 -! tau <: usize) +! counter in
          let j:usize = cast (buf.[ byte_offset ] <: u8) <: usize in
          let byte_offset:usize = byte_offset +! mk_usize 1 in
          let found:bool = j <=. i in
          let (byte_offset: usize), (found: bool), (j: usize) =
            Rust_primitives.Hax.Folds.fold_range (mk_i32 0)
              (mk_i32 256)
              (fun temp_0_ temp_1_ ->
                  let (byte_offset: usize), (found: bool), (j: usize) = temp_0_ in
                  let _:i32 = temp_1_ in
                  true)
              (byte_offset, found, j <: (usize & bool & usize))
              (fun temp_0_ e_scan ->
                  let (byte_offset: usize), (found: bool), (j: usize) = temp_0_ in
                  let e_scan:i32 = e_scan in
                  if (~.found <: bool) && (byte_offset <. mk_usize 1024 <: bool)
                  then
                    let j:usize = cast (buf.[ byte_offset ] <: u8) <: usize in
                    let byte_offset:usize = byte_offset +! mk_usize 1 in
                    let found:bool = j <=. i in
                    byte_offset, found, j <: (usize & bool & usize)
                  else byte_offset, found, j <: (usize & bool & usize))
          in
          let c:t_Array i32 (mk_usize 256) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize c i (c.[ j ] <: i32)
          in
          let sign_bit:u64 = (signs >>! counter <: u64) &. mk_u64 1 in
          let c:t_Array i32 (mk_usize 256) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize c
              j
              (if sign_bit =. mk_u64 1 <: bool
                then Hacspec_ml_dsa.Parameters.v_Q -! mk_i32 1 <: i32
                else mk_i32 1)
          in
          byte_offset, c <: (usize & t_Array i32 (mk_usize 256)))
  in
  c

#pop-options

#pop-options

#push-options "--z3rlimit 300"

/// RejNTTPoly(ρ) — FIPS 204, Algorithm 30.
/// Samples a polynomial in T_q (NTT domain) using rejection sampling
/// from SHAKE128 output.
let rej_ntt_poly (seed: t_Slice u8) : t_Array i32 (mk_usize 256) =
  let (buf: t_Array u8 (mk_usize 1024)):t_Array u8 (mk_usize 1024) =
    Hacspec_ml_dsa.Hash_functions.g (mk_usize 1024) seed
  in
  let a:t_Array i32 (mk_usize 256) = Hacspec_ml_dsa.Parameters.v_ZERO_POLY in
  let j:usize = mk_usize 0 in
  let (a: t_Array i32 (mk_usize 256)), (j: usize) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 1024 /! mk_usize 3 <: usize)
      (fun temp_0_ temp_1_ ->
          let (a: t_Array i32 (mk_usize 256)), (j: usize) = temp_0_ in
          let _:usize = temp_1_ in
          true)
      (a, j <: (t_Array i32 (mk_usize 256) & usize))
      (fun temp_0_ i ->
          let (a: t_Array i32 (mk_usize 256)), (j: usize) = temp_0_ in
          let i:usize = i in
          if j <. mk_usize 256 <: bool
          then
            match
              Hacspec_ml_dsa.Encoding.coeff_from_three_bytes (buf.[ mk_usize 3 *! i <: usize ] <: u8
                )
                (buf.[ (mk_usize 3 *! i <: usize) +! mk_usize 1 <: usize ] <: u8)
                (buf.[ (mk_usize 3 *! i <: usize) +! mk_usize 2 <: usize ] <: u8)
              <:
              Core_models.Option.t_Option i32
            with
            | Core_models.Option.Option_Some coeff ->
              let a:t_Array i32 (mk_usize 256) =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a j coeff
              in
              let j:usize = j +! mk_usize 1 in
              a, j <: (t_Array i32 (mk_usize 256) & usize)
            | _ -> a, j <: (t_Array i32 (mk_usize 256) & usize)
          else a, j <: (t_Array i32 (mk_usize 256) & usize))
  in
  a

#pop-options

#push-options "--z3rlimit 300"

/// RejBoundedPoly(ρ) — FIPS 204, Algorithm 31.
/// Samples a polynomial with coefficients in [-η, η] using rejection
/// sampling from SHAKE256 output.
let rej_bounded_poly (seed: t_Slice u8) (eta: usize) : t_Array i32 (mk_usize 256) =
  let (buf: t_Array u8 (mk_usize 512)):t_Array u8 (mk_usize 512) =
    Hacspec_ml_dsa.Hash_functions.h (mk_usize 512) seed
  in
  let a:t_Array i32 (mk_usize 256) = Hacspec_ml_dsa.Parameters.v_ZERO_POLY in
  let j:usize = mk_usize 0 in
  let (a: t_Array i32 (mk_usize 256)), (j: usize) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 512)
      (fun temp_0_ temp_1_ ->
          let (a: t_Array i32 (mk_usize 256)), (j: usize) = temp_0_ in
          let _:usize = temp_1_ in
          true)
      (a, j <: (t_Array i32 (mk_usize 256) & usize))
      (fun temp_0_ i ->
          let (a: t_Array i32 (mk_usize 256)), (j: usize) = temp_0_ in
          let i:usize = i in
          let (a: t_Array i32 (mk_usize 256)), (j: usize) =
            if j <. mk_usize 256
            then
              let z0:Core_models.Option.t_Option i32 =
                Hacspec_ml_dsa.Encoding.coeff_from_half_byte ((buf.[ i ] <: u8) &. mk_u8 15 <: u8)
                  eta
              in
              match z0 <: Core_models.Option.t_Option i32 with
              | Core_models.Option.Option_Some c ->
                let a:t_Array i32 (mk_usize 256) =
                  Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a j c
                in
                let j:usize = j +! mk_usize 1 in
                a, j <: (t_Array i32 (mk_usize 256) & usize)
              | _ -> a, j <: (t_Array i32 (mk_usize 256) & usize)
            else a, j <: (t_Array i32 (mk_usize 256) & usize)
          in
          if j <. mk_usize 256
          then
            let z1:Core_models.Option.t_Option i32 =
              Hacspec_ml_dsa.Encoding.coeff_from_half_byte ((buf.[ i ] <: u8) >>! mk_i32 4 <: u8)
                eta
            in
            match z1 <: Core_models.Option.t_Option i32 with
            | Core_models.Option.Option_Some c ->
              let a:t_Array i32 (mk_usize 256) =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a j c
              in
              let j:usize = j +! mk_usize 1 in
              a, j <: (t_Array i32 (mk_usize 256) & usize)
            | _ -> a, j <: (t_Array i32 (mk_usize 256) & usize)
          else a, j <: (t_Array i32 (mk_usize 256) & usize))
  in
  a

#pop-options

#push-options "--z3rlimit 300"

/// ExpandA(ρ) — FIPS 204, Algorithm 32.
/// Samples a k × ℓ matrix Â of polynomials in T_q from a 32-byte seed ρ.
let expand_a (v_K v_L: usize) (rho: t_Array u8 (mk_usize 32))
    : Prims.Pure (t_Array (t_Array (t_Array i32 (mk_usize 256)) v_L) v_K)
      (requires v_K <=. mk_usize 8 && v_L <=. mk_usize 8)
      (fun _ -> Prims.l_True) =
  Hacspec_ml_dsa.createi #(t_Array (t_Array i32 (mk_usize 256)) v_L)
    v_K
    #(usize -> t_Array (t_Array i32 (mk_usize 256)) v_L)
    (fun r ->
        let r:usize = r in
        Hacspec_ml_dsa.createi #(t_Array i32 (mk_usize 256))
          v_L
          #(usize -> t_Array i32 (mk_usize 256))
          (fun s ->
              let s:usize = s in
              let seed:t_Array u8 (mk_usize 34) =
                concat_2bytes rho (cast (s <: usize) <: u8) (cast (r <: usize) <: u8)
              in
              rej_ntt_poly (seed <: t_Slice u8))
        <:
        t_Array (t_Array i32 (mk_usize 256)) v_L)

#pop-options

#push-options "--z3rlimit 300"

/// ExpandS(ρ\') — FIPS 204, Algorithm 33.
/// Samples vectors s1 ∈ R^ℓ and s2 ∈ R^k with coefficients in [-η, η].
let expand_s (v_K v_L: usize) (rho_prime: t_Array u8 (mk_usize 64)) (eta: usize)
    : Prims.Pure
      (t_Array (t_Array i32 (mk_usize 256)) v_L & t_Array (t_Array i32 (mk_usize 256)) v_K)
      (requires v_K <=. mk_usize 8 && v_L <=. mk_usize 8)
      (fun _ -> Prims.l_True) =
  let (s1: t_Array (t_Array i32 (mk_usize 256)) v_L):t_Array (t_Array i32 (mk_usize 256)) v_L =
    Hacspec_ml_dsa.createi #(t_Array i32 (mk_usize 256))
      v_L
      #(usize -> t_Array i32 (mk_usize 256))
      (fun r ->
          let r:usize = r in
          let seed:t_Array u8 (mk_usize 66) = concat_u16_le rho_prime (cast (r <: usize) <: u16) in
          rej_bounded_poly (seed <: t_Slice u8) eta)
  in
  let (s2: t_Array (t_Array i32 (mk_usize 256)) v_K):t_Array (t_Array i32 (mk_usize 256)) v_K =
    Hacspec_ml_dsa.createi #(t_Array i32 (mk_usize 256))
      v_K
      #(usize -> t_Array i32 (mk_usize 256))
      (fun r ->
          let r:usize = r in
          let idx:u16 = cast (r +! v_L <: usize) <: u16 in
          let seed:t_Array u8 (mk_usize 66) = concat_u16_le rho_prime idx in
          rej_bounded_poly (seed <: t_Slice u8) eta)
  in
  s1, s2 <: (t_Array (t_Array i32 (mk_usize 256)) v_L & t_Array (t_Array i32 (mk_usize 256)) v_K)

#pop-options

#push-options "--admit_smt_queries true"

/// ExpandMask(ρ'', κ) — FIPS 204, Algorithm 34.
/// Samples a vector y ∈ R^ℓ with coefficients in [-γ1+1, γ1].
let expand_mask (v_L: usize) (rho_pp: t_Array u8 (mk_usize 64)) (kappa: usize) (gamma1: i32)
    : t_Array (t_Array i32 (mk_usize 256)) v_L =
  let c:usize =
    mk_usize 1 +!
    (Hacspec_ml_dsa.Parameters.bitlen ((cast (gamma1 <: i32) <: usize) -! mk_usize 1 <: usize)
      <:
      usize)
  in
  let out_bytes:usize = mk_usize 32 *! c in
  Hacspec_ml_dsa.createi #(t_Array i32 (mk_usize 256))
    v_L
    #(usize -> t_Array i32 (mk_usize 256))
    (fun r ->
        let r:usize = r in
        let idx:u16 = cast (kappa +! r <: usize) <: u16 in
        let seed:t_Array u8 (mk_usize 66) = concat_u16_le rho_pp idx in
        if gamma1 =. (mk_i32 1 <<! mk_i32 17 <: i32)
        then
          let (buf: t_Array u8 (mk_usize 576)):t_Array u8 (mk_usize 576) =
            Hacspec_ml_dsa.Hash_functions.h (mk_usize 576) (seed <: t_Slice u8)
          in
          Hacspec_ml_dsa.Encoding.bit_unpack (buf.[ { Core_models.Ops.Range.f_end = out_bytes }
                <:
                Core_models.Ops.Range.t_RangeTo usize ]
              <:
              t_Slice u8)
            ((cast (gamma1 <: i32) <: usize) -! mk_usize 1 <: usize)
            (cast (gamma1 <: i32) <: usize)
        else
          let (buf: t_Array u8 (mk_usize 640)):t_Array u8 (mk_usize 640) =
            Hacspec_ml_dsa.Hash_functions.h (mk_usize 640) (seed <: t_Slice u8)
          in
          Hacspec_ml_dsa.Encoding.bit_unpack (buf.[ { Core_models.Ops.Range.f_end = out_bytes }
                <:
                Core_models.Ops.Range.t_RangeTo usize ]
              <:
              t_Slice u8)
            ((cast (gamma1 <: i32) <: usize) -! mk_usize 1 <: usize)
            (cast (gamma1 <: i32) <: usize))

#pop-options
