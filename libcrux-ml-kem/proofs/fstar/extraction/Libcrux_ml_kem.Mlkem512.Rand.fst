module Libcrux_ml_kem.Mlkem512.Rand
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Rand_core in
  ()

let generate_key_pair
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng iimpl_447424039_)
      (rng: iimpl_447424039_)
     =
  let randomness:t_Array u8 (mk_usize 64) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 64) in
  let tmp0, tmp1:(iimpl_447424039_ & t_Array u8 (mk_usize 64)) =
    Rand_core.f_fill_bytes #iimpl_447424039_ #FStar.Tactics.Typeclasses.solve rng randomness
  in
  let rng:iimpl_447424039_ = tmp0 in
  let randomness:t_Array u8 (mk_usize 64) = tmp1 in
  let _:Prims.unit = () in
  let hax_temp_output:Libcrux_ml_kem.Types.t_MlKemKeyPair (mk_usize 1632) (mk_usize 800) =
    Libcrux_ml_kem.Mlkem512.generate_key_pair randomness
  in
  rng, hax_temp_output
  <:
  (iimpl_447424039_ & Libcrux_ml_kem.Types.t_MlKemKeyPair (mk_usize 1632) (mk_usize 800))

let encapsulate
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng iimpl_447424039_)
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (mk_usize 800))
      (rng: iimpl_447424039_)
     =
  let randomness:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let tmp0, tmp1:(iimpl_447424039_ & t_Array u8 (mk_usize 32)) =
    Rand_core.f_fill_bytes #iimpl_447424039_ #FStar.Tactics.Typeclasses.solve rng randomness
  in
  let rng:iimpl_447424039_ = tmp0 in
  let randomness:t_Array u8 (mk_usize 32) = tmp1 in
  let _:Prims.unit = () in
  let hax_temp_output:(Libcrux_ml_kem.Types.t_MlKemCiphertext (mk_usize 768) &
    t_Array u8 (mk_usize 32)) =
    Libcrux_ml_kem.Mlkem512.encapsulate public_key randomness
  in
  rng, hax_temp_output
  <:
  (iimpl_447424039_ &
    (Libcrux_ml_kem.Types.t_MlKemCiphertext (mk_usize 768) & t_Array u8 (mk_usize 32)))
