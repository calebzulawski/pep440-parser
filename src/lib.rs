pub mod scheme;
pub use scheme::Version;

pub mod specifiers;
pub use specifiers::{Specifier, SpecifierSet};

#[cfg(feature = "serde")]
mod serde;

use std::borrow::Cow;

/// A parsing error.
#[derive(Clone, Debug)]
pub struct Error {
    message: Cow<'static, str>,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for Error {}

impl Error {
    fn message(message: impl Into<Cow<'static, str>>) -> Self {
        Self {
            message: message.into(),
        }
    }

    fn from_nom(e: nom::error::Error<&str>) -> Self {
        Self::message(format!(
            "unexpected value encountered during parsing: {}",
            e.input.trim()
        ))
    }
}
