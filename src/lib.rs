pub mod scheme;
pub use scheme::{LocalVersion, PublicVersion};

pub mod specifiers;
pub use specifiers::Specifier;

/// A parsing error.
pub type Error = nom::error::Error<String>;
