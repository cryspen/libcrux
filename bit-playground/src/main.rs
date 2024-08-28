use libcrux_intrinsics::avx2::*;

struct D<T>(T);

use std::fmt::{Display, Error, Formatter};

impl Display for D<Vec256> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        let mut out = [0i16; 16];
        mm256_storeu_si256_i16(&mut out, self.0);
        for (i, x) in out.iter().enumerate() {
            if i > 0 {
                write!(f, " ")?;
            }
            write!(f, "{:018b}", x)?;
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
            write!(f, "{:018b}", x)?;
        }
        Ok(())
    }
}

fn mk_vec128(x7: i16, x6: i16, x5: i16, x4: i16, x3: i16, x2: i16, x1: i16, x0: i16) -> Vec128 {
    let x = mm256_set_epi16(0, 0, 0, 0, 0, 0, 0, 0, x7, x6, x5, x4, x3, x2, x1, x0);
    mm256_castsi256_si128(x)
}

fn main() {
    let x = mk_vec128(0, -1, 0, 0, 0, 0, 0, 0);
    let y = mk_vec128(0, 0, 3, 0, 0, 0, 0, 0);
    // let v = mm256_set_epi16(1, 32_767, 30_000 - 1, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8);
    println!("x {}", D(x));
    println!("y {}", D(y));
    // let x = mm256_castsi256_si128::<15>(v);
    // println!("{}", D(v));
    let v = mm_packs_epi16(x, y);
    println!("_ {}", D(v));
    // let y = bv256_castsi256_si128
}
