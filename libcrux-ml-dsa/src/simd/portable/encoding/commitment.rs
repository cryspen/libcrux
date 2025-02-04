use crate::{helper::cloop, simd::portable::vector_type::Coefficients};

#[inline(always)]
#[hax_lib::fstar::before(
    r#"
#set-options "--fuel 0 --ifuel 1 --z3rlimit 300"
"#
)]
#[hax_lib::requires(fstar!(r"Seq.length ${coefficients} == 2 /\ (forall i. bounded (Seq.index ${coefficients} i) 4)"))]
#[hax_lib::ensures(|out| fstar!(r"
let inp = bit_vec_of_int_t_array #I32 #(mk_usize 2) ${coefficients} 4 in
let out = bit_vec_of_int_t_array #U8 (MkSeq.create1 ${out}) 8 in
forall (i: nat {i < 8}). inp i == out i
"))]
fn encode_4(coefficients: &[i32]) -> u8 {
    let coefficient0 = coefficients[0] as u8;
    let coefficient1 = coefficients[1] as u8;
    (coefficient1 << 4) | coefficient0
}

#[inline(always)]
#[hax_lib::requires(fstar!(r"Seq.length ${coefficients} == 4 /\ Seq.length ${bytes} == 3 /\ 
                             (forall i. bounded (Seq.index ${coefficients} i) 6)"))]
#[hax_lib::ensures(|_| fstar!(r"
Seq.length ${bytes}_future == Seq.length ${bytes} /\
(let inp = bit_vec_of_int_t_array #I32 #(mk_usize 4) ${coefficients} 6 in
 let out = bit_vec_of_int_t_array #U8  #(mk_usize 3) ${bytes}_future 8 in
 forall (i: nat {i < 8 * 3}). inp i == out i)
"))]
fn encode_6(coefficients: &[i32], bytes: &mut [u8]) {
    let coefficient0 = coefficients[0] as u8;
    let coefficient1 = coefficients[1] as u8;
    let coefficient2 = coefficients[2] as u8;
    let coefficient3 = coefficients[3] as u8;

    let byte0 = (coefficient1 << 6) | coefficient0;
    let byte1 = (coefficient2 << 4) | coefficient1 >> 2;
    let byte2 = (coefficient3 << 2) | coefficient2 >> 4;

    bytes[0] = byte0;
    bytes[1] = byte1;
    bytes[2] = byte2;
}

#[inline(always)]
#[hax_lib::requires(fstar!(r"Seq.length ${serialized} == 4 /\ (forall i. bounded (Seq.index ${simd_unit.values} i) 4)"))]
#[hax_lib::ensures(|out| {
    let serialized_future = future(serialized);
    fstar!(r"
Seq.length ${serialized_future} == Seq.length ${serialized} /\
(let inp = bit_vec_of_int_t_array #I32 #(mk_usize 8) ${simd_unit.values} 4 in
 let out = bit_vec_of_int_t_array #U8  #(mk_usize 4) ${serialized_future} 8 in
 forall (i: nat {i < 8 * 4}). inp i == out i)
")
})]
fn serialize_4(simd_unit: &Coefficients, serialized: &mut [u8]) {
    // The commitment has coefficients in [0,15] => each coefficient occupies
    // 4 bits.
    cloop! {
        for (i, coefficients) in simd_unit.values.chunks_exact(2).enumerate() {
            hax_lib::loop_invariant!(|i: usize| {fstar!(r"
            Seq.length $serialized == 4 /\ (
              let inp = bit_vec_of_int_t_array #I32 #(mk_usize 8) ${simd_unit.values} 4 in
              let out = bit_vec_of_int_t_array #U8 #(mk_usize 4) $serialized 8 in
              forall (n: nat {n < v i * 8}). out n == inp n
            )")});

            serialized[i] = encode_4(coefficients);

            hax_lib::fstar!(r"
                let inp = bit_vec_of_int_t_array #I32 #(mk_usize 8) ${simd_unit.values} 4 in
                let out = bit_vec_of_int_t_array #U8  #(mk_usize 4) $serialized 8 in
                introduce forall (n:nat{n < 8}). inp (v i * 8 + n) == out (v i * 8 + n)
                with
                  (calc (==) {
                          inp (v i * 8 + n);
                    == {} get_bit (Seq.index ${simd_unit.values} ((v i * 8 + n) / 4)) (sz ((v i * 8 + n) % 4));
                    == { Math.Lemmas.division_addition_lemma n 4 (v i * 2) }
                          get_bit (Seq.index ${simd_unit.values} (v i * 2 + n / 4)) (sz (n % 4));
                    == {} get_bit (Seq.index $coefficients (n / 4)) (sz (n % 4));
                    == {} bit_vec_of_int_t_array #I32 #(mk_usize 2) $coefficients 4 n;
                    == {} out (v i * 8 + n);
                  })
            ");
        }
    }
    ()
}

#[inline(always)]
#[hax_lib::requires(fstar!(r"Seq.length ${serialized} == 6 /\ (forall i. bounded (Seq.index ${simd_unit.values} i) 6)"))]
#[hax_lib::ensures(|out| {
    let serialized_future = future(serialized);
    fstar!(r"
Seq.length ${serialized_future} == Seq.length ${serialized} /\
(let inp = bit_vec_of_int_t_array #I32 #(mk_usize 8) ${simd_unit.values} 6 in
 let out = bit_vec_of_int_t_array #U8  #(mk_usize 6) ${serialized_future} 8 in
 forall (i: nat {i < 8 * 6}). inp i == out i)
")
})]
pub fn serialize_6(simd_unit: &Coefficients, serialized: &mut [u8]) {
    // The commitment has coefficients in [0,43] => each coefficient occupies
    // 6 bits.

    cloop! {
        for (i, coefficients) in simd_unit.values.chunks_exact(4).enumerate() {
            hax_lib::loop_invariant!(|i: usize| {
                fstar!(
                    r"
            Seq.length $serialized == 6 /\ (
              let inp = bit_vec_of_int_t_array #I32 #(mk_usize 8) ${simd_unit.values} 6 in
              let out = bit_vec_of_int_t_array #U8 #(mk_usize 6) $serialized 8 in
              (forall (n: nat {n < v i * 24}). out n == inp n))"
                )
            });

            // TODO: use ghost state here to avoid copying
            // See: https://github.com/cryspen/libcrux/issues/783
            #[cfg(hax)]
            let mut _old_serialized: [u8; 6] = core::array::from_fn(|i| serialized[i]);

            encode_6(coefficients, &mut serialized[3 * i..3 * i + 3]);

            hax_lib::fstar!(
                r"
            let inp = bit_vec_of_int_t_array #I32 #(mk_usize 8) ${simd_unit.values} 6 in
            let out = bit_vec_of_int_t_array #U8  #(mk_usize 6) $serialized 8 in
            introduce forall (n:nat{n < 24}). inp (v i * 24 + n) == out (v i * 24 + n)
            with
                (calc (==) {
                      inp (v i * 24 + n);
                == {} get_bit (Seq.index ${simd_unit.values} ((v i * 24 + n) / 6)) (sz ((v i * 24 + n) % 6));
                == { Math.Lemmas.division_addition_lemma n 6 (v i * 4) }
                      get_bit (Seq.index ${simd_unit.values} (v i * 4 + n / 6)) (sz (n % 6));
                == {} get_bit (Seq.index $coefficients (n / 6)) (sz (n % 6));
                == {} bit_vec_of_int_t_array #I32 #(mk_usize 4) $coefficients 6 n;
                == {} out (v i * 24 + n);
                });
           (* Find a better style for these sequence updates so that such silly assertions become unnecessary *)
           assert (forall (n:nat{n >= 24 * v i /\ n < 24 * v i + 24}). inp (24 * v i + (n - 24 * v i)) == out (24 * v i + (n - 24 * v i)));
           assert (forall (n:nat{n >= 24 * v i /\ n < 24 * v i + 24}). inp n == out n);
           assert (forall (n:nat{n < v i * 24}). n / 8 < 3 * v i);
           assert (forall (j:nat{j < 3 * v i}). Seq.index ${serialized} j == Seq.index (Seq.slice ${serialized} 0 (3 * v i)) j);
           assert (forall (j:nat{j < 3 * v i}). Seq.index ${_old_serialized} j == Seq.index (Seq.slice ${_old_serialized} 0 (3 * v i)) j);
           assert (forall (n:nat{n < 24 * (v i + 1)}). inp n == out n))
        "
            );
        }
    }
    ()
}

#[inline(always)]
#[hax_lib::requires(
    fstar!(r"
        let d = Seq.length $serialized in
           (d == 4 \/ d == 6)
        /\ (forall i. bounded (Seq.index ${simd_unit.values} i) d)
    ")
)]
#[hax_lib::ensures(|out| {
    let serialized_future = future(serialized);
    fstar!(r"
let d = Seq.length ${serialized} in
( Seq.length ${serialized_future} == d /\
  (let inp = bit_vec_of_int_t_array #I32 #(mk_usize 8) ${simd_unit.values} d in
   let out = bit_vec_of_int_t_array #U8  #(mk_usize d) ${serialized_future} 8 in
   forall (i: nat {i < 8 * d}). inp i == out i))
")
})]
pub(in crate::simd::portable) fn serialize(simd_unit: &Coefficients, serialized: &mut [u8]) {
    match serialized.len() as u8 {
        4 => serialize_4(simd_unit, serialized),
        6 => serialize_6(simd_unit, serialized),
        _ => unreachable!(),
    }
}
