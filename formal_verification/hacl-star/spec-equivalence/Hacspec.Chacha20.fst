module Hacspec.Chacha20

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Hacspec.Lib

type state_t = lseq (uint32) (16)

let state_idx_t =
  nat_mod (16)

type constants_t = lseq (uint32) (4)

let constants_idx_t =
  nat_mod (4)

type block_t = lseq (uint8) (64)

type cha_cha_iv_t = lseq (uint8) (12)

type cha_cha_key_t = lseq (uint8) (32)

let chacha20_line
  (a_0 : state_idx_t)
  (b_1 : state_idx_t)
  (d_2 : state_idx_t)
  (s_3 : pos {s_3 < 32})
  (m_4 : state_t)
  : state_t =
  let state_5 : state_t =
    m_4
  in
  let state_5 =
    array_upd state_5 (a_0) (
      (array_index (state_5) (a_0)) +. (array_index (state_5) (b_1)))
  in
  let state_5 =
    array_upd state_5 (d_2) (
      (array_index (state_5) (d_2)) ^. (array_index (state_5) (a_0)))
  in
  let state_5 =
    array_upd state_5 (d_2) (
      uint32_rotate_left (array_index (state_5) (d_2)) (s_3))
  in
  state_5

let chacha20_quarter_round
  (a_6 : state_idx_t)
  (b_7 : state_idx_t)
  (c_8 : state_idx_t)
  (d_9 : state_idx_t)
  (state_10 : state_t)
  : state_t =
  let state_11 : state_t =
    chacha20_line (a_6) (b_7) (d_9) (16) (state_10)
  in
  let state_12 : state_t =
    chacha20_line (c_8) (d_9) (b_7) (12) (state_11)
  in
  let state_13 : state_t =
    chacha20_line (a_6) (b_7) (d_9) (8) (state_12)
  in
  chacha20_line (c_8) (d_9) (b_7) (7) (state_13)

let chacha20_double_round (state_14 : state_t) : state_t =
  let state_15 : state_t =
    chacha20_quarter_round (0) (4) (8) (12) (state_14)
  in
  let state_16 : state_t =
    chacha20_quarter_round (1) (5) (9) (13) (state_15)
  in
  let state_17 : state_t =
    chacha20_quarter_round (2) (6) (10) (14) (state_16)
  in
  let state_18 : state_t =
    chacha20_quarter_round (3) (7) (11) (15) (state_17)
  in
  let state_19 : state_t =
    chacha20_quarter_round (0) (5) (10) (15) (state_18)
  in
  let state_20 : state_t =
    chacha20_quarter_round (1) (6) (11) (12) (state_19)
  in
  let state_21 : state_t =
    chacha20_quarter_round (2) (7) (8) (13) (state_20)
  in
  chacha20_quarter_round (3) (4) (9) (14) (state_21)

let chacha20_rounds (state_22 : state_t) : state_t =
  let st_23 : state_t =
    state_22
  in
  let (st_23) =
    foldi (0) (10) (fun i_24 (st_23) ->
      let st_23 =
        chacha20_double_round (st_23)
      in
      (st_23))
    (st_23)
  in
  st_23

let chacha20_core (ctr_25 : uint32) (st0_26 : state_t) : state_t =
  let state_27 : state_t =
    st0_26
  in
  let state_27 =
    array_upd state_27 (12) ((array_index (state_27) (12)) +. (ctr_25))
  in
  let k_28 : state_t =
    chacha20_rounds (state_27)
  in
  (k_28) `array_add (+.)` (state_27)

let chacha20_constants_init () : constants_t =
  let constants_29 : constants_t =
    array_new_ (secret (0x0ul)) (4)
  in
  let constants_29 =
    array_upd constants_29 (0) (secret (0x61707865ul))
  in
  let constants_29 =
    array_upd constants_29 (1) (secret (0x3320646eul))
  in
  let constants_29 =
    array_upd constants_29 (2) (secret (0x79622d32ul))
  in
  let constants_29 =
    array_upd constants_29 (3) (secret (0x6b206574ul))
  in
  constants_29

let chacha20_init
  (key_30 : cha_cha_key_t)
  (iv_31 : cha_cha_iv_t)
  (ctr_32 : uint32)
  : state_t =
  let st_33 : state_t =
    array_new_ (secret (0x0ul)) (16)
  in
  let st_33 =
    array_update (st_33) (0) (chacha20_constants_init ())
  in
  let st_33 =
    array_update (st_33) (4) (array_to_le_uint32s (key_30))
  in
  let st_33 =
    array_upd st_33 (12) (ctr_32)
  in
  let st_33 =
    array_update (st_33) (13) (array_to_le_uint32s (iv_31))
  in
  st_33

let chacha20_key_block (state_34 : state_t) : block_t =
  let state_35 : state_t =
    chacha20_core (secret (0x0ul)) (state_34)
  in
  array_from_seq (64) (array_to_le_bytes (state_35))

let chacha20_key_block0
  (key_36 : cha_cha_key_t)
  (iv_37 : cha_cha_iv_t)
  : block_t =
  let state_38 : state_t =
    chacha20_init (key_36) (iv_37) (secret (0x0ul))
  in
  chacha20_key_block (state_38)

let chacha20_encrypt_block
  (st0_39 : state_t)
  (ctr_40 : uint32)
  (plain_41 : block_t)
  : block_t =
  let st_42 : state_t =
    chacha20_core (ctr_40) (st0_39)
  in
  let pl_43 : state_t =
    array_from_seq (16) (array_to_le_uint32s (plain_41))
  in
  let st_44 : state_t =
    (pl_43) `array_xor (^.)` (st_42)
  in
  array_from_seq (64) (array_to_le_bytes (st_44))

let chacha20_encrypt_last
  (st0_45 : state_t)
  (ctr_46 : uint32)
  (plain_47 : byte_seq {seq_len plain_47 < 64})
  : byte_seq =
  let b_48 : block_t =
    array_new_ (secret (pub_u8 0x0)) (64)
  in
  let b_48 =
    array_update (b_48) (0) (plain_47)
  in
  let b_48 =
    chacha20_encrypt_block (st0_45) (ctr_46) (b_48)
  in
  array_slice (b_48) (0) (seq_len (plain_47))

let chacha20_update (st0_49 : state_t) (m_50 : byte_seq) : byte_seq =
  let blocks_out_51 =
    seq_new_ (secret (pub_u8 0x0)) (seq_len (m_50))
  in
  let n_blocks_52 : uint_size =
    seq_num_exact_chunks (m_50) (64)
  in
  let blocks_out_51 =
    foldi (0) (n_blocks_52) (fun i_53 (blocks_out_51) ->
      let msg_block_54 : seq uint8 =
        seq_get_exact_chunk (m_50) (64) (i_53)
      in
      let b_55 : block_t =
        chacha20_encrypt_block (st0_49) (secret (pub_u32 (i_53))) (
          array_from_seq (64) (msg_block_54))
      in
      let blocks_out_51 =
        seq_set_exact_chunk (blocks_out_51) (64) (i_53) (b_55)
      in
      (blocks_out_51))
    (blocks_out_51)
  in
  let last_block_56 : seq uint8 =
    seq_get_remainder_chunk (m_50) (64)
  in
  let (blocks_out_51) =
    if (seq_len (last_block_56)) <> (0) then begin
      let b_57 : seq uint8 =
        chacha20_encrypt_last (st0_49) (secret (pub_u32 (n_blocks_52))) (
          last_block_56)
      in
      let blocks_out_51 =
        seq_set_chunk (blocks_out_51) (64) (n_blocks_52) (b_57)
      in
      (blocks_out_51)
    end else begin (blocks_out_51)
    end
  in
  blocks_out_51

let chacha20
  (key_58 : cha_cha_key_t)
  (iv_59 : cha_cha_iv_t)
  (ctr_60 : pub_uint32)
  (m_61 : byte_seq)
  : byte_seq =
  let state_62 : state_t =
    chacha20_init (key_58) (iv_59) (secret (ctr_60))
  in
  chacha20_update (state_62) (m_61)

