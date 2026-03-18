/// Encoding and decoding of ML-DSA keys, signatures, and polynomials.
/// FIPS 204, Sections 7.1–7.2 (Algorithms 9–28).
///
/// These functions perform bit-level packing and are marked opaque for F*
/// extraction since they involve dynamic allocation and bit manipulation.

use crate::parameters::{Polynomial, MlDsaParams, Q, D, ZERO_POLY, bitlen};

// ========================================================================
// Bit-packing — Algorithms 16–21
// ========================================================================

/// SimpleBitPack(w, b) — Algorithm 16.
///
/// Packs polynomial w (coefficients in [0, b]) into 32·bitlen(b) bytes.
#[hax_lib::opaque]
pub(crate) fn simple_bit_pack(w: &Polynomial, b: usize) -> Vec<u8> {
    let bits = bitlen(b);
    let total_bits = 256 * bits;
    let total_bytes = (total_bits + 7) / 8;
    let mut out = vec![0u8; total_bytes];
    let mut bit_pos = 0usize;
    for i in 0..256 {
        let val = w[i] as u32;
        for bit in 0..bits {
            if (val >> bit) & 1 == 1 {
                out[bit_pos / 8] |= 1 << (bit_pos % 8);
            }
            bit_pos += 1;
        }
    }
    out
}

/// BitPack(w, a, b) — Algorithm 17.
///
/// Packs polynomial w (coefficients in [-a, b]) into 32·bitlen(a+b) bytes.
/// Stores b - w_i for each coefficient.
#[hax_lib::opaque]
pub(crate) fn bit_pack(w: &Polynomial, a: usize, b: usize) -> Vec<u8> {
    let bits = bitlen(a + b);
    let total_bits = 256 * bits;
    let total_bytes = (total_bits + 7) / 8;
    let mut out = vec![0u8; total_bytes];
    let mut bit_pos = 0usize;
    for i in 0..256 {
        let val = (b as i32 - w[i]) as u32;
        for bit in 0..bits {
            if (val >> bit) & 1 == 1 {
                out[bit_pos / 8] |= 1 << (bit_pos % 8);
            }
            bit_pos += 1;
        }
    }
    out
}

/// SimpleBitUnpack(v, b) — Algorithm 18.
///
/// Unpacks bytes into a polynomial with coefficients in [0, 2^c - 1] where c = bitlen(b).
#[hax_lib::opaque]
pub(crate) fn simple_bit_unpack(v: &[u8], b: usize) -> Polynomial {
    let bits = bitlen(b);
    let mut w = ZERO_POLY;
    let mut bit_pos = 0usize;
    for i in 0..256 {
        let mut val = 0u32;
        for bit in 0..bits {
            if bit_pos / 8 < v.len() && (v[bit_pos / 8] >> (bit_pos % 8)) & 1 == 1 {
                val |= 1 << bit;
            }
            bit_pos += 1;
        }
        w[i] = val as i32;
    }
    w
}

/// BitUnpack(v, a, b) — Algorithm 19.
///
/// Unpacks bytes into a polynomial with coefficients in [b - 2^c + 1, b]
/// where c = bitlen(a + b). When a + b + 1 is a power of 2, coefficients are in [-a, b].
#[hax_lib::opaque]
pub(crate) fn bit_unpack(v: &[u8], a: usize, b: usize) -> Polynomial {
    let bits = bitlen(a + b);
    let mut w = ZERO_POLY;
    let mut bit_pos = 0usize;
    for i in 0..256 {
        let mut val = 0u32;
        for bit in 0..bits {
            if bit_pos / 8 < v.len() && (v[bit_pos / 8] >> (bit_pos % 8)) & 1 == 1 {
                val |= 1 << bit;
            }
            bit_pos += 1;
        }
        w[i] = b as i32 - val as i32;
    }
    w
}

// ========================================================================
// Hint encoding — Algorithms 20–21
// ========================================================================

/// HintBitPack(h) — Algorithm 20.
///
/// Encodes hint vector h (k polynomials with binary coefficients,
/// collectively at most ω nonzero) into ω + k bytes.
#[hax_lib::opaque]
pub(crate) fn hint_bit_pack<const K: usize>(h: &[[bool; 256]; K], omega: usize) -> Vec<u8> {
    let mut y = vec![0u8; omega + K];
    let mut index = 0usize;
    for i in 0..K {
        for j in 0..256 {
            if h[i][j] {
                y[index] = j as u8;
                index += 1;
            }
        }
        y[omega + i] = index as u8;
    }
    y
}

/// HintBitUnpack(y, omega) — Algorithm 21.
///
/// Decodes hint vector from ω + k bytes. Returns None if malformed.
#[hax_lib::opaque]
pub(crate) fn hint_bit_unpack<const K: usize>(y: &[u8], omega: usize) -> Option<[[bool; 256]; K]> {
    let mut h = [[false; 256]; K];
    let mut index = 0usize;
    for i in 0..K {
        let end = y[omega + i] as usize;
        if end < index || end > omega {
            return None;
        }
        let first = index;
        while index < end {
            if index > first && y[index - 1] >= y[index] {
                return None;
            }
            h[i][y[index] as usize] = true;
            index += 1;
        }
    }
    // Check remaining bytes are zero
    for i in index..omega {
        if y[i] != 0 {
            return None;
        }
    }
    Some(h)
}

// ========================================================================
// Key and signature encoding — Algorithms 22–28
// ========================================================================

/// pkEncode(ρ, t1) — Algorithm 22.
#[hax_lib::opaque]
pub(crate) fn pk_encode<const K: usize, const PK_SIZE: usize>(
    rho: &[u8; 32], t1: &[Polynomial; K],
) -> [u8; PK_SIZE] {
    let t1_bits = bitlen(Q as usize - 1) - D; // = 10
    let mut pk = rho.to_vec();
    for i in 0..K {
        pk.extend(simple_bit_pack(&t1[i], (1 << t1_bits) - 1));
    }
    pk.try_into().unwrap_or_else(|v: Vec<u8>| {
        panic!("pk_encode: expected {} bytes, got {}", PK_SIZE, v.len())
    })
}

/// pkDecode(pk) — Algorithm 23.
#[hax_lib::opaque]
pub(crate) fn pk_decode<const K: usize>(pk: &[u8]) -> ([u8; 32], [Polynomial; K]) {
    let t1_bits = bitlen(Q as usize - 1) - D; // = 10
    let bytes_per_poly = 32 * t1_bits; // = 320
    let mut rho = [0u8; 32];
    rho.copy_from_slice(&pk[..32]);
    let mut t1 = [ZERO_POLY; K];
    for i in 0..K {
        let start = 32 + i * bytes_per_poly;
        t1[i] = simple_bit_unpack(&pk[start..start + bytes_per_poly], (1 << t1_bits) - 1);
    }
    (rho, t1)
}

/// skEncode(ρ, K, tr, s1, s2, t0) — Algorithm 24.
#[hax_lib::opaque]
pub(crate) fn sk_encode<const K: usize, const L: usize, const SK_SIZE: usize>(
    rho: &[u8; 32], key: &[u8; 32], tr: &[u8; 64],
    s1: &[Polynomial; L], s2: &[Polynomial; K], t0: &[Polynomial; K],
    params: &MlDsaParams,
) -> [u8; SK_SIZE] {
    let eta = params.eta;
    let mut sk = Vec::new();
    sk.extend_from_slice(rho);
    sk.extend_from_slice(key);
    sk.extend_from_slice(tr);
    for i in 0..L {
        sk.extend(bit_pack(&s1[i], eta, eta));
    }
    for i in 0..K {
        sk.extend(bit_pack(&s2[i], eta, eta));
    }
    let d_minus_1 = D - 1;
    for i in 0..K {
        sk.extend(bit_pack(&t0[i], (1 << d_minus_1) - 1, 1 << d_minus_1));
    }
    sk.try_into().unwrap_or_else(|v: Vec<u8>| {
        panic!("sk_encode: expected {} bytes, got {}", SK_SIZE, v.len())
    })
}

/// skDecode(sk) — Algorithm 25.
#[hax_lib::opaque]
pub(crate) fn sk_decode<const K: usize, const L: usize>(
    sk: &[u8], params: &MlDsaParams,
) -> ([u8; 32], [u8; 32], [u8; 64], [Polynomial; L], [Polynomial; K], [Polynomial; K]) {
    let eta = params.eta;
    let eta_bytes = 32 * bitlen(2 * eta);

    let mut rho = [0u8; 32];
    rho.copy_from_slice(&sk[..32]);
    let mut key = [0u8; 32];
    key.copy_from_slice(&sk[32..64]);
    let mut tr = [0u8; 64];
    tr.copy_from_slice(&sk[64..128]);

    let mut offset = 128;
    let mut s1 = [ZERO_POLY; L];
    for i in 0..L {
        s1[i] = bit_unpack(&sk[offset..offset + eta_bytes], eta, eta);
        offset += eta_bytes;
    }
    let mut s2 = [ZERO_POLY; K];
    for i in 0..K {
        s2[i] = bit_unpack(&sk[offset..offset + eta_bytes], eta, eta);
        offset += eta_bytes;
    }

    let d_minus_1 = D - 1;
    let t0_bytes = 32 * bitlen((1 << d_minus_1) - 1 + (1 << d_minus_1));
    let mut t0 = [ZERO_POLY; K];
    for i in 0..K {
        t0[i] = bit_unpack(&sk[offset..offset + t0_bytes], (1 << d_minus_1) - 1, 1 << d_minus_1);
        offset += t0_bytes;
    }
    (rho, key, tr, s1, s2, t0)
}

/// sigEncode(c̃, z, h) — Algorithm 26.
#[hax_lib::opaque]
pub(crate) fn sig_encode<const K: usize, const L: usize, const SIG_SIZE: usize>(
    c_tilde: &[u8], z: &[Polynomial; L], h: &[[bool; 256]; K],
    params: &MlDsaParams,
) -> [u8; SIG_SIZE] {
    let gamma1 = params.gamma1 as usize;
    let mut sigma = c_tilde.to_vec();
    for i in 0..L {
        sigma.extend(bit_pack(&z[i], gamma1 - 1, gamma1));
    }
    sigma.extend(hint_bit_pack(h, params.omega));
    sigma.try_into().unwrap_or_else(|v: Vec<u8>| {
        panic!("sig_encode: expected {} bytes, got {}", SIG_SIZE, v.len())
    })
}

/// sigDecode(σ) — Algorithm 27.
///
/// Returns (c̃, z, h) or None if the hint is malformed.
#[hax_lib::opaque]
pub(crate) fn sig_decode<const K: usize, const L: usize>(
    sigma: &[u8], params: &MlDsaParams,
) -> Option<(Vec<u8>, [Polynomial; L], [[bool; 256]; K])> {
    let gamma1 = params.gamma1 as usize;
    let c_tilde_len = params.lambda / 4;
    let z_bytes = 32 * bitlen(gamma1 - 1 + gamma1);

    let c_tilde = sigma[..c_tilde_len].to_vec();
    let mut offset = c_tilde_len;
    let mut z = [ZERO_POLY; L];
    for i in 0..L {
        z[i] = bit_unpack(&sigma[offset..offset + z_bytes], gamma1 - 1, gamma1);
        offset += z_bytes;
    }
    let h = hint_bit_unpack::<K>(&sigma[offset..], params.omega)?;
    Some((c_tilde, z, h))
}

/// w1Encode(w1) — Algorithm 28.
///
/// Encodes the high-bits vector w1 into bytes for hashing.
#[hax_lib::opaque]
pub(crate) fn w1_encode<const K: usize>(w1: &[Polynomial; K], params: &MlDsaParams) -> Vec<u8> {
    let w1_max = ((Q - 1) / (2 * params.gamma2) - 1) as usize;
    let mut encoded = Vec::new();
    for i in 0..K {
        encoded.extend(simple_bit_pack(&w1[i], w1_max));
    }
    encoded
}

// ========================================================================
// CoeffFromThreeBytes, CoeffFromHalfByte — Algorithms 14–15
// ========================================================================

/// CoeffFromThreeBytes(b0, b1, b2) — Algorithm 14.
///
/// Returns an element of {0, 1, ..., q-1} or None (rejection).
pub(crate) fn coeff_from_three_bytes(b0: u8, b1: u8, b2: u8) -> Option<i32> {
    let b2p = if b2 > 127 { b2 - 128 } else { b2 };
    let z = ((b2p as i32) << 16) | ((b1 as i32) << 8) | (b0 as i32);
    if z < Q { Some(z) } else { None }
}

/// CoeffFromHalfByte(b, η) — Algorithm 15.
///
/// Returns an element of {-η, ..., η} or None (rejection).
pub(crate) fn coeff_from_half_byte(b: u8, eta: usize) -> Option<i32> {
    if eta == 2 && (b as usize) < 15 {
        Some(2 - (b % 5) as i32)
    } else if eta == 4 && (b as usize) < 9 {
        Some(4 - b as i32)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_bit_pack_unpack_roundtrip() {
        let mut w = ZERO_POLY;
        w[0] = 1023; // max for 10-bit
        w[1] = 0;
        w[255] = 512;
        let packed = simple_bit_pack(&w, 1023);
        let unpacked = simple_bit_unpack(&packed, 1023);
        for i in 0..256 {
            assert_eq!(w[i], unpacked[i], "mismatch at {i}");
        }
    }

    #[test]
    fn bit_pack_unpack_roundtrip() {
        let mut w = ZERO_POLY;
        w[0] = 2;
        w[1] = -2;
        w[2] = 0;
        w[3] = 1;
        let packed = bit_pack(&w, 2, 2);
        let unpacked = bit_unpack(&packed, 2, 2);
        for i in 0..256 {
            assert_eq!(w[i], unpacked[i], "mismatch at {i}");
        }
    }

    #[test]
    fn coeff_from_three_bytes_basic() {
        assert_eq!(coeff_from_three_bytes(0, 0, 0), Some(0));
        assert_eq!(coeff_from_three_bytes(1, 0, 0), Some(1));
        // q-1 = 8380416 = 0x7FE000, so (0x00, 0xE0, 0x7F) should be accepted
        assert_eq!(coeff_from_three_bytes(0x00, 0xE0, 0x7F), Some(Q - 1));
        // b2=128 > 127 → b2'=0, z=0, accepted
        assert_eq!(coeff_from_three_bytes(0, 0, 128), Some(0));
        // q = 8380417 = 0x7FE001, so (0x01, 0xE0, 0x7F) gives z = q, rejected
        assert_eq!(coeff_from_three_bytes(0x01, 0xE0, 0x7F), None);
    }

    #[test]
    fn coeff_from_half_byte_eta2() {
        assert_eq!(coeff_from_half_byte(0, 2), Some(2));
        assert_eq!(coeff_from_half_byte(4, 2), Some(-2));
        assert_eq!(coeff_from_half_byte(14, 2), Some(2 - 14 % 5)); // 2 - 4 = -2
        assert_eq!(coeff_from_half_byte(15, 2), None); // rejection
    }
}
