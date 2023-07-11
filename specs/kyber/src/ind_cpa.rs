use crate::encoding::*;
use crate::ring::*;
use crate::sampling::*;
use crate::parameters;

use libcrux::digest;

// XOF = SHAKE-128;
// H = SHA3-256;
// G = SHA3-512;
// PRF(s, b) = SHAKE-256(s||b)
#[allow(non_snake_case)]
pub(crate) fn key_gen(d : &[u8]) -> ([u8; parameters::CPA_PKE_PUBLIC_KEY_BYTES], [u8; parameters::CPA_PKE_SECRET_KEY_BYTES]) {
    let mut xof_input : [u8; 34] = [0; 34];
    let mut prf_input : [u8; 33] = [0; 33];

    let mut A = [[RingElement::ZERO; parameters::K], 
                 [RingElement::ZERO; parameters::K], 
                 [RingElement::ZERO; parameters::K]];

    let mut s = [RingElement::ZERO; parameters::K];
    let mut e = [RingElement::ZERO; parameters::K];

    let mut s_hat = [RingElement::ZERO; parameters::K];
    let mut e_hat = [RingElement::ZERO; parameters::K];

    let mut N : u8 = 0;

    // Using constants due to:
    // https://github.com/hacspec/hacspec-v2/issues/27
    let mut pk : [u8; 1184] = [0; 1184];
    let mut sk : [u8; 1152] = [0; 1152];

    let mut jump : usize = 0;

    let hashed = digest::sha3_512(&d); // G(d)
    let (rho, sigma) = hashed.split_at(32);

    for i in 0..rho.len() {
        xof_input[i] = rho[i];
    }
    for i in 0..parameters::K {
        for j in 0..parameters::K {
            xof_input[32] = i.try_into().unwrap();
            xof_input[33] = j.try_into().unwrap();

            // Using a constant here due to:
            // and https://github.com/hacspec/hacspec-v2/issues/27
            let xof_bytes : [u8; 2304] = digest::shake128::<2304>(&xof_input);

            A[i][j] = parse(xof_bytes).unwrap();
        }
    }

    for i in 0..sigma.len() {
        prf_input[i] = sigma[i];
    }
    for i in 0..parameters::K {
        prf_input[32] = N;

        // Using a constant value due to:
        // https://github.com/hacspec/hacspec-v2/issues/27
        let prf_output = digest::shake256::<128>(&prf_input);

        s[i] = cbd(prf_output);

        N += 1;
    }

    for i in 0..parameters::K {
        prf_input[32] = N;

        // Using a constant value due to:
        // https://github.com/hacspec/hacspec-v2/issues/27
        let prf_output = digest::shake256::<128>(&prf_input);

        e[i] = cbd(prf_output);

        N += 1;
    }

    for i in 0..s.len() {
        s_hat[i] = s[i].ntt_representation();
    }

    for i in 0..e.len() {
        e_hat[i] = e[i].ntt_representation();
    }

    let mut t_hat = multiply_A_transpose_by_s(&A, &s_hat);
    for i in 0..t_hat.len() {
        t_hat[i] = t_hat[i].add(&e_hat[i]);
    }

    for i in 0..t_hat.len() {
        let encoded = encode(&t_hat[i]);
        for j in 0..encoded.len() {
            pk[jump + j] = encoded[j];
        }

        jump += encoded.len();
    }

    for i in 0..rho.len() {
        pk[jump + i] = rho[i];
    }

    jump = 0;

    for i in 0..s_hat.len() {
        let encoded = encode(&s_hat[i]);
        for j in 0..encoded.len() {
            sk[jump + j] = encoded[j];
        }
        jump += encoded.len();
    }

    return (pk, sk);
}
