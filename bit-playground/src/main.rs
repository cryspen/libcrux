use libcrux_intrinsics::avx2::*;
use rand::prelude::*;

struct D<T>(T);

use std::fmt::{Display, Error, Formatter};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BV(pub Vec<u8>);
trait ToBitVec {
    fn to_bit_vec(&self) -> BV;
}
trait FromBitVec: Sized {
    fn from_bit_vec(bv: &BV) -> Self;
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

#[test]
fn conv256() {
    for i in 0..10 {
        let abv = BV::rand::<256>();
        let a: Vec256 = abv.clone().to();
        if (a.to_bit_vec() != abv) {
            println!("abv = {}", abv);
            println!("a   = {}", a.to_bit_vec());
            panic!();
        }
    }
}

#[test]
fn conv128() {
    for i in 0..10 {
        let abv = BV::rand::<128>();
        let a: Vec128 = abv.clone().to();
        if (a.to_bit_vec() != abv) {
            println!("abv = {}", abv);
            println!("a   = {}", a.to_bit_vec());
            panic!();
        }
    }
}

impl BV {
    fn to<T: FromBitVec>(&self) -> T {
        T::from_bit_vec(self)
    }
}

impl<T: ToBitVec> From<T> for BV {
    fn from(x: T) -> Self {
        x.to_bit_vec()
    }
}

impl BV {
    fn rand<const N: usize>() -> Self {
        bv_of_fn::<N>(|_| if rand::random() { 1 } else { 0 })
    }
}

impl FromBitVec for Vec256 {
    fn from_bit_vec(bv: &BV) -> Self {
        assert!(bv.0.len() == 256);
        let x: Vec<_> =
            bv.0.chunks(16)
                .map(|inner| i16::from_bit_vec(&BV(inner.to_vec())))
                .rev()
                .collect();
        mm256_set_epi16(
            x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7], x[8], x[9], x[10], x[11], x[12], x[13],
            x[14], x[15],
        )
    }
}

impl FromBitVec for Vec128 {
    fn from_bit_vec(bv: &BV) -> Self {
        assert!(bv.0.len() == 128);
        let x: Vec<_> =
            bv.0.chunks(16)
                .map(|inner| i16::from_bit_vec(&BV(inner.to_vec())))
                .collect();
        mk_vec128(x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7])
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
        // let bv: [u8; 16] = std::array::from_fn(|i| (((*self as u16) >> i) % 2) as u8);
    }
}
impl FromBitVec for i16 {
    fn from_bit_vec(bv: &BV) -> i16 {
        let mut out: u16 = 0;
        for bit in bv.0.iter().cloned().rev() {
            out = (out << 1) + bit as u16;
        }
        out as i16
    }
}
impl FromBitVec for i32 {
    fn from_bit_vec(bv: &BV) -> i32 {
        let mut out: i32 = 0;
        for bit in bv.0.iter().cloned().rev() {
            out = (out << 1) + bit as i32;
        }
        out as i32
    }
}

impl ToBitVec for Vec256 {
    fn to_bit_vec(&self) -> BV {
        let mut out = [0i16; 16];
        mm256_storeu_si256_i16(&mut out, *self);
        (&out[..]).to_bit_vec()
    }
}

impl BV {
    fn print(&self) -> String {
        self.0
            .iter()
            .cloned()
            .map(|i| format!("{i}"))
            .collect::<Vec<_>>()
            .join("")
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

fn mk_vec128(x7: i16, x6: i16, x5: i16, x4: i16, x3: i16, x2: i16, x1: i16, x0: i16) -> Vec128 {
    let x = mm256_set_epi16(0, 0, 0, 0, 0, 0, 0, 0, x0, x1, x2, x3, x4, x5, x6, x7);
    mm256_castsi256_si128(x)
}

fn bv_of_fn<const N: usize>(f: impl FnMut(usize) -> u8) -> BV {
    let out: [u8; N] = core::array::from_fn(f);
    BV(out.to_vec())
}

fn bv256_slli_epi16(shift: usize, y: BV) -> BV {
    assert!(y.0.len() == 256);
    bv_of_fn::<256>(|i| {
        let nth_bit = i % 16;
        if nth_bit >= shift {
            y.0[i - shift]
        } else {
            0
        }
    })
}

#[test]
fn bv256_slli_epi16_test() {
    for i in 0..100000 {
        let abv = BV::rand::<256>();
        let a = abv.clone().to();
        let rbv = bv256_slli_epi16(15, abv.clone());
        let r = mm256_slli_epi16::<15>(a);
        let r = r.to_bit_vec();
        if r != rbv {
            println!("abv = {}", abv);
            println!("a   = {}", a.to_bit_vec());
            println!("rbv = {}", rbv);
            println!("r   = {}", r);
            panic!();
        }
    }
}

fn bv256_castsi256_si128(bv: BV) -> BV {
    assert!(bv.0.len() == 256);
    bv_of_fn::<128>(|i| bv.0[i])
}

#[test]
fn bv256_castsi256_si128_test() {
    for i in 0..100000 {
        let abv = BV::rand::<256>();
        let a = abv.clone().to();
        let rbv = bv256_castsi256_si128(abv.clone());
        let r = mm256_castsi256_si128(a);
        let r = r.to_bit_vec();
        if r != rbv {
            println!("abv = {}", abv);
            println!("a   = {}", a.to_bit_vec());
            println!("rbv = {}", rbv);
            println!("r   = {}", r);
            panic!();
        }
    }
}

fn bv256_extracti128_si256(bv: BV) -> BV {
    assert!(bv.0.len() == 256);
    let mut out = [0u8; 128];
    bv_of_fn::<128>(|i| bv.0[i + 128])
}

#[test]
fn bv256_extracti128_si256_test() {
    for i in 0..100000 {
        let abv = BV::rand::<256>();
        let a = abv.clone().to();
        let rbv = bv256_extracti128_si256(abv.clone());
        let r = mm256_extracti128_si256::<1>(a);
        let r = r.to_bit_vec();
        if r != rbv {
            println!("abv = {}", abv);
            println!("a   = {}", a.to_bit_vec());
            println!("rbv = {}", rbv);
            println!("r   = {}", r);
            panic!();
        }
    }
}

fn bv_movemask_epi8_bv(a: BV) -> BV {
    assert!(a.0.len() == 128);
    bv_of_fn::<128>(|j| if j < 16 { a.0[(j * 8) + 7] } else { 0 })
}

fn bv_movemask_epi8(a: BV) -> i32 {
    i32::from_bit_vec(&bv_movemask_epi8_bv(a))
}

#[test]
fn bv_movemask_epi8_test() {
    for i in 0..100000 {
        let abv = BV::rand::<128>();
        let a = abv.clone().to();
        let rbv = bv_movemask_epi8(abv.clone());
        let r = mm_movemask_epi8(a);
        if r != rbv {
            println!("abv = {}", abv);
            println!("a   = {}", a.to_bit_vec());
            println!("rbv = {}", rbv);
            println!("r   = {}", r);
            panic!();
        }
    }
}

fn bv_packs_epi16(x: BV, y: BV) -> BV {
    assert!(x.0.len() == 128);
    assert!(y.0.len() == 128);
    bv_of_fn::<128>(|i| {
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
        saturated.0[i - offset8]
    })
}

#[test]
fn bv_packs_epi16_test() {
    for i in 0..100000 {
        let abv = BV::rand::<128>();
        let a = abv.clone().to();
        let bbv = BV::rand::<128>();
        let b = bbv.clone().to();
        let rbv = bv_packs_epi16(abv.clone(), bbv.clone());
        let r = mm_packs_epi16(a, b);
        let r = r.to_bit_vec();
        if r != rbv {
            println!("abv = {}", abv);
            println!("a   = {}", a.to_bit_vec());
            println!("bbv = {}", abv);
            println!("b   = {}", a.to_bit_vec());
            println!("rbv = {}", rbv);
            println!("r   = {}", r);
            panic!();
        }
    }
}

fn saturate8(bv: BV) -> BV {
    assert!(bv.0.len() == 16);
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
    bv_of_fn::<16>(|i| {
        let last_bit = i == 7;
        if negative {
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
    })
}

impl BV {
    fn from<const N: usize>(s: &str) -> Self {
        let result = BV(s
            .chars()
            .map(|ch| match ch {
                '0' => 0,
                '1' => 1,
                _ => panic!("Expected only 1 or 0, got `{ch}`"),
            })
            .collect());
        if result.0.len() != N {
            panic!(
                "Expected a bit vector of size {N}, got a bit vector of size {}",
                result.0.len()
            );
        }
        result
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let result = match &args.iter().map(|s| s.as_str()).collect::<Vec<_>>()[..] {
        ["mm256_slli_epi16", "15", vec] => {
            let bv = BV::from::<256>(vec);
            let result = mm256_slli_epi16::<15>(Vec256::from_bit_vec(&bv));
            result.to_bit_vec().print()
        }
        ["mm256_castsi256_si128", vec] => {
            let bv = BV::from::<256>(vec);
            let result = mm256_castsi256_si128(Vec256::from_bit_vec(&bv));
            result.to_bit_vec().print()
        }
        ["mm256_extracti128_si256", "1", vec] => {
            let bv = BV::from::<256>(vec);
            let result = mm256_extracti128_si256::<1>(Vec256::from_bit_vec(&bv));
            result.to_bit_vec().print()
        }
        ["mm_packs_epi16", a, b] => {
            let a = BV::from::<128>(a);
            let b = BV::from::<128>(b);
            let result = mm_packs_epi16(Vec128::from_bit_vec(&a), Vec128::from_bit_vec(&b));
            result.to_bit_vec().print()
        }
        ["rand", n] => {
            let n = n.parse::<usize>().unwrap();
            (0..n)
                .map(|_| match rand::random::<bool>() {
                    true => "1",
                    false => "0",
                })
                .collect::<Vec<_>>()
                .join("")
        }
        // ["mm_movemask_epi8", a] => {
        //     let a = BV::from::<128>(a);
        //     let result = mm_movemask_epi8(Vec128::from_bit_vec(&a));
        //     result.to_bit_vec().print()
        // }
        _ => panic!("Cannot handle {args:#?} x"),
    };
    println!("{result}");

    // // for i in i16::MIN..i16::MAX {
    // for i in i16::MIN..i16::MAX {
    //     let x = mk_vec128(i, 0, 0, 0, 0, 0, 0, 0);
    //     let y = mk_vec128(0, 0, 0, 0, 0, 0, 0, 0);
    //     let r = mm_packs_epi16(x, y);
    //     let xbv = x.to_bit_vec();
    //     let ybv = y.to_bit_vec();
    //     let rbv = bv_packs_epi16(xbv.clone(), ybv.clone());
    //     if (r.to_bit_vec() == rbv) {
    //     } else {
    //         println!("");
    //         println!("i={i}");
    //         println!(
    //             "saturated8({})={}",
    //             i.to_bit_vec(),
    //             saturate8(i.to_bit_vec())
    //         );
    //         if (r.to_bit_vec() == rbv) {
    //             println!("================");
    //         } else {
    //             println!("!!!!!!!!!!!!!!!!");
    //         }
    //         println!("xbv {}", xbv.clone());
    //         println!("r   {}", r.to_bit_vec());
    //         println!("rbv {}", rbv.clone());
    //     }
    //     // assert!(r.to_bit_vec() == rbv);
    // }

    // let bv = format!("{}", r.to_bit_vec());
    // let bv_ = "0000000000000000 0000000000000000 0000000000000000 0111111100000000 0000000000000000 0000000000000000 0000000000000000 0000000000000000";
    // assert_eq!(bv, bv_);
    // let x = mm256_castsi256_si128::<15>(v);
    // println!("{}", D(v));
    // let y = bv256_castsi256_si128
}
