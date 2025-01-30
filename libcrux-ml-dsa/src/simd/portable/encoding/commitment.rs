use crate::{helper::cloop, simd::portable::vector_type::Coefficients};

#[inline(always)]
#[hax_lib::fstar::before(
    r#"
#set-options "--fuel 0 --ifuel 1 --z3rlimit 300 --z3version 4.13.3 --ext context_pruning"
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
#[hax_lib::requires(fstar!(r"Seq.length ${coefficients} == 4 /\ (forall i. bounded (Seq.index ${coefficients} i) 6)"))]
#[hax_lib::ensures(|out| fstar!(r"
let inp = bit_vec_of_int_t_array #I32 #(mk_usize 4) ${coefficients} 6 in
let out = bit_vec_of_int_t_array #U8 (MkSeq.create3 ${out}) 8 in
forall (i: nat {i < 8 * 3}). inp i == out i
"))]
fn encode_6(coefficients: &[i32]) -> (u8, u8, u8) {
    let coefficient0 = coefficients[0] as u8;
    let coefficient1 = coefficients[1] as u8;
    let coefficient2 = coefficients[2] as u8;
    let coefficient3 = coefficients[3] as u8;

    (
        (coefficient1 << 6) | coefficient0,
        (coefficient2 << 4) | coefficient1 >> 2,
        (coefficient3 << 2) | coefficient2 >> 4,
    )
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

        let (r0, r1, r2) = encode_6(coefficients);
        serialized[3 * i] = r0;
        serialized[3 * i + 1] = r1;
        serialized[3 * i + 2] = r2;

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
                })
        "
        );
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
