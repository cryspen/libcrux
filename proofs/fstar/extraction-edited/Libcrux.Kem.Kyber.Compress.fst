module Libcrux.Kem.Kyber.Compress
#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"
open Core
open FStar.Mul

let compress_message_coefficient fe =
  let (shifted: i16):i16 = 1664s -! (cast (fe <: u16) <: i16) in
  assert (v shifted == 1664 - v fe);
  let mask:i16 = shifted >>! 15l in
  assert (v mask = v shifted / pow2 15);
  assert (if v shifted < 0 then mask = ones else mask = zero);
  let shifted_to_positive:i16 = mask ^. shifted in
  logxor_lemma shifted mask;
  assert (v shifted < 0 ==> v shifted_to_positive = v (lognot shifted));
  neg_equiv_lemma shifted;
  assert (v (lognot shifted) = -(v shifted) -1);
  assert (v shifted >= 0 ==> v shifted_to_positive = v (mask `logxor` shifted));
  assert (v shifted >= 0 ==> mask = zero);
  assert (v shifted >= 0 ==> mask ^. shifted = shifted);
  assert (v shifted >= 0 ==> v shifted_to_positive = v shifted);
  assert (shifted_to_positive >=. 0s);
  let shifted_positive_in_range:i16 = shifted_to_positive -! 832s in
  assert (1664 - v fe >= 0 ==> v shifted_positive_in_range == 832 - v fe);
  assert (1664 - v fe < 0 ==> v shifted_positive_in_range == -2497 + v fe);
  let r0 = shifted_positive_in_range >>! 15l in
  let r1 = r0 &. 1s in
  let res = cast (r1) <: u8 in
  assert (v r0 = v shifted_positive_in_range / pow2 15);
  assert (if v shifted_positive_in_range < 0 then r0 = ones else r0 = zero);
  logand_lemma 1s r0; 
  assert (if v shifted_positive_in_range < 0 then r1 = 1s else r1 = 0s);
  assert ((v fe >= 833 && v fe <= 2496) ==> r1 = 1s);
  assert (v fe < 833 ==> r1 = 0s);
  assert (v fe > 2496 ==> r1 = 0s);
  assert (v res = v r1);
  res

let compress_ciphertext_coefficient coefficient_bits fe =
  let _:Prims.unit = () <: Prims.unit in
  let _:Prims.unit = () <: Prims.unit in
  let compressed:u32 = (cast (fe <: u16) <: u32) <<! (coefficient_bits +! 1uy <: u8) in
  let compressed:u32 =
    compressed +! (cast (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) <: u32)
  in
  let compressed:u32 =
    compressed /! (cast (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <<! 1l <: i32) <: u32)
  in
  let res = cast (Libcrux.Kem.Kyber.Arithmetic.get_n_least_significant_bits coefficient_bits compressed <: u32
    )
  <:
  i32
  in
  res

#push-options "--z3rlimit 300"
let decompress_ciphertext_coefficient coefficient_bits fe =
  let _:Prims.unit = () <: Prims.unit in
  let _:Prims.unit = () <: Prims.unit in
  assert (v (1ul <<! coefficient_bits) <= pow2 11);
  assert (v fe < pow2 11);
  let decompressed:u32 =
    (cast (fe <: i32) <: u32) *! (cast (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) <: u32)
  in
  let decompressed:u32 = (decompressed <<! 1l <: u32) +! (1ul <<! coefficient_bits <: u32) in
  let decompressed:u32 = decompressed >>! (coefficient_bits +! 1uy <: u8) in
  let res = cast (decompressed <: u32) <: i32 in
  let res : Libcrux.Kem.Kyber.Arithmetic.i32_b 3328 = res in
  res

let decompress_message_coefficient fe =
  let res = (Core.Ops.Arith.Neg.neg fe <: i32) &.
             ((Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS +! 1l <: i32) /! 2l <: i32) in
  assert (v ((Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS +! 1l <: i32) /! 2l <: i32) == 1665);
  assert (res == logand #i32_inttype (Core.Ops.Arith.Neg.neg fe) 1665l);
  assert (v fe == 0 ==> Core.Ops.Arith.Neg.neg fe = zero);
  logand_lemma 1665l zero;
  assert (v fe == 0 ==> res == zero);
  res <: Libcrux.Kem.Kyber.Arithmetic.i32_b 3328
#pop-options
