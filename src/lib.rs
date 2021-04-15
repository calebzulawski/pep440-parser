pub mod version;
pub use version::Version;

/// A parsing error.
pub type Error = nom::error::Error<String>;
