//! #Libjade Rust bindings

mod bindings;
pub use bindings::*;

// Function definitions for things not compiled in certain configurations.
mod fallback_definitions;
pub use fallback_definitions::*;
