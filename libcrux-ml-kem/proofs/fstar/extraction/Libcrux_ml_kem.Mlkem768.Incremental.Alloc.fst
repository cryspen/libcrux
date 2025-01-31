module Libcrux_ml_kem.Mlkem768.Incremental.Alloc
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let generate_key_pair (randomness: t_Array u8 (mk_usize 64)) =
  Rust_primitives.unsize (Rust_primitives.unsize (Libcrux_ml_kem.Ind_cca.Incremental.Multiplexing.Alloc.generate_keypair
            (mk_usize 3)
            (mk_usize 1152)
            (mk_usize 2400)
            (mk_usize 1184)
            (mk_usize 1152)
            (mk_usize 2)
            (mk_usize 128)
            randomness
          <:
          Alloc.Boxed.t_Box (dyn 1 (fun z -> Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Keys z))
            Alloc.Alloc.t_Global)
      <:
      Alloc.Boxed.t_Box (dyn 1 (fun z -> Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Keys z))
        Alloc.Alloc.t_Global)

let encapsulate1
      (public_key_part: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey1)
      (randomness: t_Array u8 (mk_usize 32))
     =
  Libcrux_ml_kem.Ind_cca.Incremental.Multiplexing.Alloc.encapsulate1 (mk_usize 3) (mk_usize 1088)
    (mk_usize 960) (mk_usize 10) (mk_usize 320) (mk_usize 2) (mk_usize 128) (mk_usize 2)
    (mk_usize 128) public_key_part randomness

let encapsulate2
      (state: dyn 1 (fun z -> Libcrux_ml_kem.Ind_cca.Incremental.Types.t_State z))
      (public_key_part: t_Slice u8)
     =
  Libcrux_ml_kem.Ind_cca.Incremental.Multiplexing.Alloc.encapsulate2 (mk_usize 3)
    (mk_usize 1152)
    (mk_usize 128)
    (mk_usize 4)
    (Rust_primitives.unsize state
      <:
      dyn 1 (fun z -> Libcrux_ml_kem.Ind_cca.Incremental.Types.t_State z))
    public_key_part

let decapsulate
      (private_key: dyn 1 (fun z -> Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Keys z))
      (ciphertext1: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 (mk_usize 960))
      (ciphertext2: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext2 (mk_usize 128))
     =
  Libcrux_ml_kem.Ind_cca.Incremental.Multiplexing.Alloc.decapsulate (mk_usize 3) (mk_usize 2400)
    (mk_usize 1152) (mk_usize 1184) (mk_usize 1088) (mk_usize 1152) (mk_usize 960) (mk_usize 128)
    (mk_usize 10) (mk_usize 4) (mk_usize 320) (mk_usize 2) (mk_usize 128) (mk_usize 2)
    (mk_usize 128) (mk_usize 1120)
    (Rust_primitives.unsize private_key
      <:
      dyn 1 (fun z -> Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Keys z)) ciphertext1 ciphertext2
