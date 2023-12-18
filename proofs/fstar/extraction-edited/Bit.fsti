module Bit
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type bit = n: nat {n < 2}

/// Mathematical `get_bit` definition on `nat`s
let get_bit_nat (x: nat) (nth: nat): bit
  = (x / pow2 nth) % 2

/// `get_bit` definition for machine integer of any size and signedness
[@"opaque_to_smt"]
let get_bit (#n: inttype) (x: int_t n) (nth: usize {v nth < bits n}): bit
  = if v x >= 0 then get_bit_nat (v x) (v nth)
               else // two's complement
                    get_bit_nat (pow2 (bits n) + v x) (v nth)

unfold let bit_and (x y: bit): bit = match x, y with | (1, 1) -> 1 | _ -> 0
unfold let bit_or  (x y: bit): bit = (x + y) % 2

/// Bit-wise semantics for `&.`
val get_bit_and #t (x y: int_t t) (i: usize {v i < bits t})
  : Lemma (get_bit (x &. y) i == get_bit x i `bit_and` get_bit y i)
          [SMTPat (get_bit (x &. y) i)]

/// Bit-wise semantics for `|.`
val get_bit_or #t (x y: int_t t) (i: usize {v i < bits t})
  : Lemma (get_bit (x |. y) i == get_bit x i `bit_or` get_bit y i)
          [SMTPat (get_bit (x |. y) i)]

/// Bit-wise semantics for `<<!`
val get_bit_shl #t #u (x: int_t t) (y: int_t u) (i: usize {v i < bits t})
  : Lemma (requires v y >= 0 /\ v y < bits t)
          (ensures get_bit (x <<! y) i 
                == (if v i < v y then 0 else get_bit x (mk_int (v i - v y))))
    [SMTPat (get_bit (x <<! y) i)]

/// Bit-wise semantics for `>>!`
val get_bit_shr #t #u (x: int_t t) (y: int_t u) (i: usize {v i < bits t})
  : Lemma (requires v y >= 0 /\ v y < bits t)
          (ensures get_bit (x >>! y) i 
                == (if v i < bits t - v y
                    then get_bit x (mk_int (v i + v y))
                    else if signed t
                         then get_bit x (mk_int (bits t - 1))
                         else 0))
    [SMTPat (get_bit (x >>! y) i)]

/// Number of bits carried by an integer of type `t`
type bit_num t = d: usize {v d > 0 /\ v d <= bits t}

/// Integer of type `t` that carries `d` bits
type int_t_b t (d: bit_num t) = 
  n: int_t t {forall (i: usize). (v i < bits t /\ v i >= v d) ==> get_bit n i == 0}

/// `get_bit` within an array of integers carrying `d` bits each
#push-options "--fuel 0 --ifuel 1 --z3rlimit 50"
let get_bit_arr (#n: inttype) (#len: usize) 
                (arr: t_Array (int_t n) len)
                (d: bit_num n)
                (nth: usize {v nth < v len * v d}): bit
  = get_bit Libcrux.Kem.Kyber.Arithmetic.(arr.[nth /! d]) (nth %! d)
#pop-options

/// Same as `get_bit_arr`, but inputs are `nat`s instead of `usize`s
let get_bit_arr_nat (#n: inttype) (#len: nat {len < max_usize})
                    (arr: t_Array (int_t n) (sz len))
                    (d: nat {d > 0 /\ d <= bits n})
                    (nth: nat {nth < len * d /\ nth < max_usize}): bit
  = get_bit_arr arr (mk_int d) (mk_int nth)

/// Create a bit vector given an array of integers carrying `d` bits each
let bit_vector (#n: inttype) (#len: usize)
               (arr: t_Array (int_t n) len)
               (d: bit_num n): t_Array bit (len *. d)
  = Libcrux.Kem.Kyber.Arithmetic.createi (len *. d) (get_bit_arr arr d)

/// Bit-wise semantics of `2^n-1`
val get_bit_pow2_minus_one #t
  (n: nat {pow2 n - 1 <= maxint t}) 
  (nth: usize {v nth < bits t})
  : Lemma (  get_bit (mk_int #t (pow2 n - 1)) nth
          == (if v nth < n then 1 else 0))

/// Log2 table
unfold let mask_inv_opt =
  function | 0   -> Some 0
           | 1   -> Some 1
           | 3   -> Some 2
           | 7   -> Some 3
           | 15  -> Some 4
           | 31  -> Some 5
           | 63  -> Some 6
           | 127 -> Some 7
           | 255 -> Some 8
           | _   -> None

/// Specialized `get_bit_pow2_minus_one` lemmas with SMT patterns
/// targetting machine integer literals of type `i32`
val get_bit_pow2_minus_one_i32
  (x: int {Some? (mask_inv_opt x)}) (nth: usize {v nth < 32})
  : Lemma ( get_bit (FStar.Int32.int_to_t x) nth 
        == (if v nth < Some?.v (mask_inv_opt x) then 1 else 0))
  [SMTPat (get_bit (FStar.Int32.int_to_t x) nth)]

/// Specialized `get_bit_pow2_minus_one` lemmas with SMT patterns
/// targetting machine integer literals of type `u8`  
val get_bit_pow2_minus_one_u8
  (t: _ {t == u8_inttype}) (x: int {Some? (mask_inv_opt x)}) (nth: usize {v nth < 8})
  : Lemma ( get_bit #t (FStar.UInt8.uint_to_t x) nth 
        == (if v nth < Some?.v (mask_inv_opt x) then 1 else 0))
  [SMTPat (get_bit #t (FStar.UInt8.uint_to_t x) nth)]

/// Bit-wise semantics of integer casts
val get_bit_cast #t #u
  (x: int_t t) (nth: usize)
  : Lemma (requires v nth < bits u /\ v nth < bits t)
          (ensures get_bit x nth == get_bit (cast x <: int_t u) nth)
          [SMTPat (get_bit (cast #(int_t t) #(int_t u) x <: int_t u) nth)]

val get_last_bit_signed_lemma (#t: inttype{signed t}) (x: int_t t)
  : Lemma (   get_bit x (mk_int (bits t - 1)) 
          == (if v x < 0 then 1 else 0))
    // [SMTPat (get_bit x (mk_int (bits t - 1)))]
