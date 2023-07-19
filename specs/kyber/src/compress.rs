use crate::helpers::field::FieldElement;
use crate::parameters::KyberPolynomialRingElement;

impl<const MODULUS: u16> FieldElement<MODULUS> {
    pub fn compress(&self, to_bit_size : u8) -> Self {
        let compression_factor : f64 = f64::from(2u16.pow(u32::from(to_bit_size))) / f64::from(Self::MODULUS);

        let compressed : u16 = ((compression_factor * f64::from(self.value)).round() as u16) % Self::MODULUS;

        Self {
            value: compressed,
            bits_to_represent_value: to_bit_size.try_into().unwrap(),
        }
    }

    pub fn decompress(&self, to_bit_size : u8) -> Self {
        let decompression_factor : f64 = f64::from(Self::MODULUS) / f64::from(2u16.pow(u32::from(to_bit_size)));

        let decompressed : u16 = (decompression_factor * f64::from(self.value)).round() as u16;

        Self {
            value: decompressed,
            bits_to_represent_value: to_bit_size.try_into().unwrap(),
        }
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
