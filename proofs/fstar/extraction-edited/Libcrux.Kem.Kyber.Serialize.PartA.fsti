module Libcrux.Kem.Kyber.Serialize.PartA
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul
open MkSeq

let int_arr_bitwise_eq
       #t1 #t2 #n1 #n2
       (arr1: t_Array (int_t t1) n1)
       (d1: bit_num t1)
       (arr2: t_Array (int_t t2) n2)
       (d2: bit_num t2 {v n1 * d1 == v n2 * d2})
     = forall i. i < v n1 * d1
       ==> bit_vec_of_int_arr arr1 d1 i == bit_vec_of_int_arr arr2 d2 i

val compress_coefficients_10_ (coefficient1 coefficient2 coefficient3 coefficient4: i32)
    : Prims.Pure (u8 & u8 & u8 & u8 & u8) 
      (requires True)
      (ensures fun tuple ->
         int_arr_bitwise_eq
                (create4 (coefficient1, coefficient2, coefficient3, coefficient4)) 10
                (create5 tuple) 8
      )

val compress_coefficients_11_
      (coefficient1 coefficient2 coefficient3 coefficient4 coefficient5 coefficient6 coefficient7 coefficient8:
          int_t_d i32_inttype 11)
    : Prims.Pure (u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8 & u8)
      (requires True)
      (ensures fun tuple ->
         int_arr_bitwise_eq
                (create8 (coefficient1, coefficient2, coefficient3, coefficient4, coefficient5, coefficient6, coefficient7, coefficient8)) 11
                (create11 tuple) 8
      )

val compress_coefficients_3_ (coefficient1 coefficient2: int_t_d u16_inttype 12)
    : Prims.Pure (u8 & u8 & u8)
    (requires True)
    (ensures fun tuple ->
       int_arr_bitwise_eq
              (create2 (coefficient1, coefficient2)) 12
              (create3 tuple) 8
    )

val compress_coefficients_5_
      (coefficient2 coefficient1 coefficient4 coefficient3 coefficient5 coefficient7 coefficient6 coefficient8: int_t_d u8_inttype 5)
    : Prims.Pure (u8 & u8 & u8 & u8 & u8)
      (requires True)
      (ensures fun tuple ->
         int_arr_bitwise_eq
                (create8 (coefficient1, coefficient2, coefficient3, coefficient4, coefficient5, coefficient6, coefficient7, coefficient8)) 5
                (create5 tuple) 8
      )

val decompress_coefficients_10_ (byte2 byte1 byte3 byte4 byte5: int_t_d i32_inttype 8)
    : Prims.Pure (i32 & i32 & i32 & i32)
      (requires True)
      (ensures fun tuple ->
         int_arr_bitwise_eq
                (create5 (byte1, byte2, byte3, byte4, byte5)) 8
                (create4 tuple) 10
      )

val decompress_coefficients_11_
      (byte2 byte1 byte3 byte5 byte4 byte6 byte7 byte9 byte8 byte10 byte11: int_t_d i32_inttype 8)
    : Prims.Pure (i32 & i32 & i32 & i32 & i32 & i32 & i32 & i32)
      (requires True)
      (ensures fun tuple ->
         int_arr_bitwise_eq
                (create11 (byte1, byte2, byte3, byte4, byte5, byte6, byte7, byte8, byte9, byte10, byte11)) 8
                (create8 tuple) 11
      )

val decompress_coefficients_4_ (byte: u8)
    : Prims.Pure (i32 & i32) 
      (requires True)
      (ensures fun tuple ->
         int_arr_bitwise_eq
                (create1 byte) 8
                (create2 tuple) 4
      )

val decompress_coefficients_5_ (byte1 byte2 byte3 byte4 byte5: int_t_d i32_inttype 5)
    : Prims.Pure (i32 & i32 & i32 & i32 & i32 & i32 & i32 & i32)
      (requires True)
      (ensures fun tuple ->
         int_arr_bitwise_eq
                (create5 (byte1, byte2, byte3, byte4, byte5)) 8
                (create8 tuple) 5
      )
