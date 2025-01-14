/// Used to classify arrays, usually of scalars.
///
/// It might make sense to require that the type inside the array is a Scalar. If we do that we can
/// also ask that Scalar implements Clone + Default, which would make the type bounds a bit simpler
pub mod array;
pub mod slice;

pub use array::*;
pub use slice::*;

// TODO: Scalars (m256 etc)
