module Libcrux_ml_kem.Mlkem768.Rand
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Rand_core in
  ()

/// Encapsulate ML-KEM 768
/// Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
/// The input is a reference to an [`MlKem768PublicKey`].
/// The random number generator `rng` needs to implement `RngCore` and
/// `CryptoRng` to sample the required randomness internally.
val encapsulate
      (#impl_277843321_: Type0)
      {| i1: Rand_core.t_RngCore impl_277843321_ |}
      {| i2: Rand_core.t_CryptoRng impl_277843321_ |}
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1184))
      (rng: impl_277843321_)
    : Prims.Pure
      (impl_277843321_ & (Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 1088) & t_Array u8 (sz 32)))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Generate ML-KEM 768 Key Pair
/// The random number generator `rng` needs to implement `RngCore` and
/// `CryptoRng` to sample the required randomness internally.
/// This function returns an [`MlKem768KeyPair`].
val generate_key_pair
      (#impl_277843321_: Type0)
      {| i1: Rand_core.t_RngCore impl_277843321_ |}
      {| i2: Rand_core.t_CryptoRng impl_277843321_ |}
      (rng: impl_277843321_)
    : Prims.Pure (impl_277843321_ & Libcrux_ml_kem.Types.t_MlKemKeyPair (sz 2400) (sz 1184))
      Prims.l_True
      (fun _ -> Prims.l_True)
