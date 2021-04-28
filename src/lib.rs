pub mod scheme;
pub use scheme::{LocalVersion, PublicVersion};

pub mod specifiers;
pub use specifiers::{Specifier, SpecifierSet};

#[cfg(feature = "serde")]
mod serde;

/// A parsing error.
pub type Error = nom::error::Error<String>;
