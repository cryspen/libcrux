use libcrux_intrinsics::avx2::*;

struct D<T>(T);

use std::fmt::{Display, Error, Formatter};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BV(pub Vec<u8>);
trait ToBitVec {
    fn to_bit_vec(&self) -> BV;
}
impl ToBitVec for &[i16] {
    fn to_bit_vec(&self) -> BV {
        let mut bits = vec![];
        for mut input in self.into_iter().cloned() {
            let mut input_bits = vec![];
            for i in 0..16 {
                input_bits.push(((input as u16) % 2) as u8);
                input = input >> 1;
            }
            for bit in input_bits.into_iter() {
                bits.push(bit);
            }
        }
        BV(bits)
    }
}

impl ToBitVec for Vec128 {
    fn to_bit_vec(&self) -> BV {
        let mut out = [0i16; 8];
        mm_storeu_si128(&mut out, *self);
        (&out[..]).to_bit_vec()
    }
}
impl ToBitVec for i16 {
    fn to_bit_vec(&self) -> BV {
        (&[*self][..]).to_bit_vec()
    }
}

impl ToBitVec for Vec256 {
    fn to_bit_vec(&self) -> BV {
        let mut out = [0i16; 16];
        mm256_storeu_si256_i16(&mut out, *self);
        (&out[..]).to_bit_vec()
    }
}

impl Display for BV {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        for i in 0..self.0.len() {
            if i > 0 && i % 16 == 0 {
                write!(f, " ");
            }
            write!(f, "{}", self.0[i]);
        }
        Ok(())
    }
}

impl Display for D<Vec256> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        let mut out = [0i16; 16];
        mm256_storeu_si256_i16(&mut out, self.0);
        for (i, x) in out.iter().enumerate() {
            if i > 0 {
                write!(f, " ")?;
            }
            write!(f, "{:016b}", x)?;
        }
        Ok(())
    }
}
impl Display for D<Vec128> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        let mut out = [0i16; 8];
        mm_storeu_si128(&mut out, self.0);
        for (i, x) in out.iter().enumerate() {
            if i > 0 {
                write!(f, " ")?;
            }
            write!(f, "{:016b}", x)?;
        }
        Ok(())
    }
}

fn bv_packs_epi16(x: BV, y: BV) -> BV {
    assert!(x.0.len() == 128);
    assert!(y.0.len() == 128);
    let mut out = [0; 128];
    for i in 0..128 {
        let nth_block = i / 8;
        let offset8 = nth_block * 8;
        let offset16_ = nth_block * 16;
        let offset16 = offset16_ % 128;
        let v = if offset16_ < 128 {
            x.clone()
        } else {
            y.clone()
        };
        let block = BV(v.0[offset16..offset16 + 16].to_vec());
        let saturated = saturate8(block.clone());
        out[i] = saturated.0[i - offset8];
        // out[offset8..offset8 + 8]
        //     .copy_from_slice(&saturate8(BV(v.0[offset16..offset16 + 16].to_vec())).0[..]);
    }
    BV(out.to_vec())
}

fn mk_vec128(x7: i16, x6: i16, x5: i16, x4: i16, x3: i16, x2: i16, x1: i16, x0: i16) -> Vec128 {
    let x = mm256_set_epi16(0, 0, 0, 0, 0, 0, 0, 0, x0, x1, x2, x3, x4, x5, x6, x7);
    mm256_castsi256_si128(x)
}

fn saturate8_verbose(bv: BV) -> BV {
    assert!(bv.0.len() == 16);
    let mut out = BV([0u8; 8].to_vec());
    let upper_bits_any = bv.0[7]
        | bv.0[8]
        | bv.0[9]
        | bv.0[10]
        | bv.0[11]
        | bv.0[12]
        | bv.0[13]
        | bv.0[14]
        | bv.0[15];
    let upper_bits_all = bv.0[7]
        & bv.0[8]
        & bv.0[9]
        & bv.0[10]
        & bv.0[11]
        & bv.0[12]
        & bv.0[13]
        & bv.0[14]
        & bv.0[15];
    if bv.0[15] == 1 {
        if upper_bits_all > 0 {
            for i in 0..8 {
                out.0[i] = bv.0[i];
            }
        }
        out.0[7] = 1;
    } else {
        if upper_bits_any > 0 {
            for i in 0..7 {
                out.0[i] = 1;
            }
        } else {
            for i in 0..8 {
                out.0[i] = bv.0[i];
            }
        }
    }
    out
}

fn saturate8(bv: BV) -> BV {
    assert!(bv.0.len() == 16);
    let mut out = BV([0u8; 8].to_vec());
    let any1 = bv.0[7] == 1
        || bv.0[8] == 1
        || bv.0[9] == 1
        || bv.0[10] == 1
        || bv.0[11] == 1
        || bv.0[12] == 1
        || bv.0[13] == 1
        || bv.0[14] == 1
        || bv.0[15] == 1;
    let all1 = bv.0[7] == 1
        && bv.0[8] == 1
        && bv.0[9] == 1
        && bv.0[10] == 1
        && bv.0[11] == 1
        && bv.0[12] == 1
        && bv.0[13] == 1
        && bv.0[14] == 1
        && bv.0[15] == 1;

    let negative = bv.0[15] == 1;
    for i in 0..8 {
        let last_bit = i == 7;
        out.0[i] = if negative {
            if last_bit {
                1
            } else {
                if all1 {
                    bv.0[i]
                } else {
                    0
                }
            }
        } else {
            if any1 {
                if last_bit {
                    0
                } else {
                    1
                }
            } else {
                bv.0[i]
            }
        }
    }
    out
}

fn main() {
    // for i in i16::MIN..i16::MAX {
    for i in i16::MIN..i16::MAX {
        let x = mk_vec128(i, 0, 0, 0, 0, 0, 0, 0);
        let y = mk_vec128(0, 0, 0, 0, 0, 0, 0, 0);
        let r = mm_packs_epi16(x, y);
        let xbv = x.to_bit_vec();
        let ybv = y.to_bit_vec();
        let rbv = bv_packs_epi16(xbv.clone(), ybv.clone());
        if (r.to_bit_vec() == rbv) {
        } else {
            println!("");
            println!("i={i}");
            println!(
                "saturated8({})={}",
                i.to_bit_vec(),
                saturate8(i.to_bit_vec())
            );
            if (r.to_bit_vec() == rbv) {
                println!("================");
            } else {
                println!("!!!!!!!!!!!!!!!!");
            }
            println!("xbv {}", xbv.clone());
            println!("r   {}", r.to_bit_vec());
            println!("rbv {}", rbv.clone());
        }
        // assert!(r.to_bit_vec() == rbv);
    }

    // let bv = format!("{}", r.to_bit_vec());
    // let bv_ = "0000000000000000 0000000000000000 0000000000000000 0111111100000000 0000000000000000 0000000000000000 0000000000000000 0000000000000000";
    // assert_eq!(bv, bv_);
    // let x = mm256_castsi256_si128::<15>(v);
    // println!("{}", D(v));
    // let y = bv256_castsi256_si128
}
