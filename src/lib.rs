pub mod scheme;
pub use scheme::{LocalVersion, PublicVersion};

/// A parsing error.
pub type Error = nom::error::Error<String>;
