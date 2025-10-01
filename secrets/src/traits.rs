/// A trait for public types that can be classified into secret types
pub trait Classify {
    /// The secret type that this public type can be classified into
    type Classified;
    /// Convert this public value into a secret value
    fn classify(self) -> Self::Classified;
}

/// A trait for classifying immutable references to public types
pub trait ClassifyRef {
    /// The secret reference type that this public reference can be classified into
    type ClassifiedRef;
    /// Convert this public reference into a secret reference
    fn classify_ref(self) -> Self::ClassifiedRef;
}

/// A trait for declassifying secret types into public types
pub trait Declassify {
    /// The public type that this secret type can be declassified into
    type Declassified;
    /// Convert this secret value into a public value
    fn declassify(self) -> Self::Declassified;
}

/// A trait for declassifying references to secret types
pub trait DeclassifyRef {
    /// The public reference type that this secret reference can be declassified into
    type DeclassifiedRef;
    /// Convert this secret reference into a public reference
    fn declassify_ref(self) -> Self::DeclassifiedRef;
}

/// A trait for classifying mutable references to public types
pub trait ClassifyRefMut {
    /// The secret mutable reference type that this public mutable reference can be classified into
    type ClassifiedRefMut;
    /// Convert this public mutable reference into a secret mutable reference
    fn classify_ref_mut(self) -> Self::ClassifiedRefMut;
}

/// A trait for declassifying mutable references to secret types
pub trait DeclassifyRefMut {
    /// The public mutable reference type that this secret mutable reference can be declassified into
    type DeclassifiedRefMut;
    /// Convert this secret mutable reference into a public mutable reference
    fn declassify_ref_mut(self) -> Self::DeclassifiedRefMut;
}

/// Marker trait for scalar types (machine integers)
pub trait Scalar: Copy {}

impl Scalar for u8 {}
impl Scalar for u16 {}
impl Scalar for u32 {}
impl Scalar for u64 {}
#[cfg(not(eurydice))]
impl Scalar for u128 {}

impl Scalar for i8 {}
impl Scalar for i16 {}
impl Scalar for i32 {}
impl Scalar for i64 {}
#[cfg(not(eurydice))]
impl Scalar for i128 {}

/// A trait for integer operations provided by Rust for machine integers
pub trait IntOps
where
    Self: Sized,
{
    /// Addition with wrapping overflow behavior
    fn wrapping_add<T: Into<Self>>(self, rhs: T) -> Self;
    /// Subtraction with wrapping overflow behavior
    fn wrapping_sub<T: Into<Self>>(self, rhs: T) -> Self;
    /// Multiplication with wrapping overflow behavior
    fn wrapping_mul<T: Into<Self>>(self, rhs: T) -> Self;
    /// Rotate the bits of the integer to the left
    fn rotate_left(self, rhs: u32) -> Self;
    /// Rotate the bits of the integer to the right
    fn rotate_right(self, rhs: u32) -> Self;
}

/// A trait for byte conversion operations provided by Rust for machine integers
pub trait EncodeOps<T, const N: usize> {
    /// Convert to little-endian byte array
    fn to_le_bytes(&self) -> [T; N];
    /// Convert to big-endian byte array
    fn to_be_bytes(&self) -> [T; N];

    /// Create from little-endian byte array
    fn from_le_bytes(x: [T; N]) -> Self;
    /// Create from big-endian byte array
    fn from_be_bytes(x: [T; N]) -> Self;
}

// SIMD values are also scalars
#[cfg(target_arch = "x86")]
impl Scalar for core::arch::x86::__m128i {}

#[cfg(target_arch = "x86")]
impl Scalar for core::arch::x86::__m256i {}

#[cfg(target_arch = "x86")]
impl Scalar for core::arch::x86::__m256 {}

#[cfg(target_arch = "x86_64")]
impl Scalar for core::arch::x86_64::__m128i {}

#[cfg(target_arch = "x86_64")]
impl Scalar for core::arch::x86_64::__m256i {}

#[cfg(target_arch = "x86_64")]
impl Scalar for core::arch::x86_64::__m256 {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::int8x8_t {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::int8x16_t {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::int16x4_t {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::int16x8_t {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::int32x2_t {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::int32x4_t {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::int64x1_t {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::int64x2_t {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::uint8x8_t {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::uint8x16_t {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::uint16x4_t {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::uint16x8_t {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::uint32x2_t {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::uint32x4_t {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::uint64x1_t {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::uint64x2_t {}
