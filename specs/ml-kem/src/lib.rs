// This module is declared here since otherwise, hax reports the following error:
//
// The THIR body of item
// DefId(0:313 ~ hacspec_kyber[4591]::parameters::KyberFieldElement::{constant#0})
// was stolen.
//
// This is being tracked in https://github.com/hacspec/hacspec-v2/issues/27
mod parameters;


mod compress;
mod ind_cca;
mod ind_cpa;
mod invert_ntt;
mod matrix;
mod ntt;
mod polynomial;
mod sampling;
mod serialize;

pub use parameters::{
    MlKemParams, ML_KEM_1024, ML_KEM_1024_CT_SIZE, ML_KEM_1024_DK_PKE_SIZE, ML_KEM_1024_DK_SIZE,
    ML_KEM_1024_EK_SIZE, ML_KEM_1024_J_INPUT_SIZE, ML_KEM_512, ML_KEM_512_CT_SIZE,
    ML_KEM_512_DK_PKE_SIZE, ML_KEM_512_DK_SIZE, ML_KEM_512_EK_SIZE, ML_KEM_512_J_INPUT_SIZE,
    ML_KEM_768, ML_KEM_768_CT_SIZE, ML_KEM_768_DK_PKE_SIZE, ML_KEM_768_DK_SIZE, ML_KEM_768_EK_SIZE,
    ML_KEM_768_J_INPUT_SIZE,
};
pub use sampling::BadRejectionSamplingRandomnessError;

pub use ind_cca::{decapsulate, encapsulate, generate_keypair, public_key_modulus_check};
