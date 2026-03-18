/// FIPS 204 — Module-Lattice-Based Digital Signature Standard (ML-DSA).
///
/// This is a pure functional specification of ML-DSA, intended for
/// extraction to F* via hax for formal verification.

mod parameters;
mod hash_functions;
mod arithmetic;
mod ntt;
mod polynomial;
mod matrix;
mod encoding;
mod sampling;
mod ml_dsa;

pub use parameters::{
    MlDsaParams, ML_DSA_44, ML_DSA_65, ML_DSA_87,
    ML_DSA_44_PK_SIZE, ML_DSA_44_SK_SIZE, ML_DSA_44_SIG_SIZE,
    ML_DSA_65_PK_SIZE, ML_DSA_65_SK_SIZE, ML_DSA_65_SIG_SIZE,
    ML_DSA_87_PK_SIZE, ML_DSA_87_SK_SIZE, ML_DSA_87_SIG_SIZE,
    ML_DSA_44_W1_SIZE, ML_DSA_65_W1_SIZE, ML_DSA_87_W1_SIZE,
    ML_DSA_44_C_TILDE_LEN, ML_DSA_65_C_TILDE_LEN, ML_DSA_87_C_TILDE_LEN,
    pk_size, sig_size,
};
pub use ml_dsa::{keygen_internal, sign_internal, verify_internal};

/// Utility function to create an array of size `N` by applying a function `f` to each index.
#[hax_lib::fstar::replace(
    r#"
assume val createi
      (#v_T: Type0)
      (v_N: usize)
      (#v_F: Type0)
      (f: (x:usize{x <. v_N}) -> v_T)
    : t_Array v_T v_N

assume val createi_lemma
      (#v_T: Type0)
      (v_N: usize)
      (#v_F: Type0)
      (f: (x:usize{x <. v_N}) -> v_T)
      (i: usize{i <. v_N})
     : Lemma (Seq.index (createi #v_T v_N #v_F f) (v i) == f i)
       [SMTPat (Seq.index (createi #v_T v_N #v_F f) (v i))]
"#
)]
pub(crate) fn createi<T, const N: usize, F: Fn(usize) -> T>(f: F) -> [T; N] {
    core::array::from_fn(f)
}
