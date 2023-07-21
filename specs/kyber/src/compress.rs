use crate::parameters::KyberFieldElement;
use crate::parameters::KyberPolynomialRingElement;
use crate::helpers::field::FieldElement;

impl KyberFieldElement {
    pub fn compress(&self, to_bit_size : u8) -> Self {
        let compression_factor : f64 = f64::from(2u16.pow(u32::from(to_bit_size))) / f64::from(Self::MODULUS);

        let compressed : u16 = ((compression_factor * f64::from(self.value)).round() as u16) % Self::MODULUS;

        compressed.into()
    }

    pub fn decompress(&self, to_bit_size : u8) -> Self {
        let decompression_factor : f64 = f64::from(Self::MODULUS) / f64::from(2u16.pow(u32::from(to_bit_size)));

        let decompressed : u16 = (decompression_factor * f64::from(self.value)).round() as u16;

        decompressed.into()
    }
}

impl KyberPolynomialRingElement {
    pub fn compress(&self, bits_per_compressed_coefficient : u8) -> Self {
        KyberPolynomialRingElement {
            coefficients: self.coefficients.map(|coefficient| coefficient.compress(bits_per_compressed_coefficient))
        }
    }
    pub fn decompress(&self, bits_per_compressed_coefficient : u8) -> Self {
        KyberPolynomialRingElement {
            coefficients: self.coefficients.map(|coefficient| coefficient.decompress(bits_per_compressed_coefficient))
        }
    }
}
