module Libcrux_ml_kem.Mlkem768.Rand
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Rand_core in
  ()

let encapsulate
      (#impl_277843321_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_RngCore impl_277843321_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Rand_core.t_CryptoRng impl_277843321_)
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (mk_usize 1184))
      (rng: impl_277843321_)
     =
  let randomness:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let tmp0, tmp1:(impl_277843321_ & t_Array u8 (mk_usize 32)) =
    Rand_core.f_fill_bytes #impl_277843321_ #FStar.Tactics.Typeclasses.solve rng randomness
  in
  let rng:impl_277843321_ = tmp0 in
  let randomness:t_Array u8 (mk_usize 32) = tmp1 in
  let _:Prims.unit = () in
  let hax_temp_output:(Libcrux_ml_kem.Types.t_MlKemCiphertext (mk_usize 1088) &
    t_Array u8 (mk_usize 32)) =
    Libcrux_ml_kem.Mlkem768.encapsulate public_key randomness
  in
  rng, hax_temp_output
  <:
  (impl_277843321_ &
    (Libcrux_ml_kem.Types.t_MlKemCiphertext (mk_usize 1088) & t_Array u8 (mk_usize 32)))

let generate_key_pair
      (#impl_277843321_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_RngCore impl_277843321_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Rand_core.t_CryptoRng impl_277843321_)
      (rng: impl_277843321_)
     =
  let randomness:t_Array u8 (mk_usize 64) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 64) in
  let tmp0, tmp1:(impl_277843321_ & t_Array u8 (mk_usize 64)) =
    Rand_core.f_fill_bytes #impl_277843321_ #FStar.Tactics.Typeclasses.solve rng randomness
  in
  let rng:impl_277843321_ = tmp0 in
  let randomness:t_Array u8 (mk_usize 64) = tmp1 in
  let _:Prims.unit = () in
  let hax_temp_output:Libcrux_ml_kem.Types.t_MlKemKeyPair (mk_usize 2400) (mk_usize 1184) =
    Libcrux_ml_kem.Mlkem768.generate_key_pair randomness
  in
  rng, hax_temp_output
  <:
  (impl_277843321_ & Libcrux_ml_kem.Types.t_MlKemKeyPair (mk_usize 2400) (mk_usize 1184))
