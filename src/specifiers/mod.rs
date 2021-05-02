//! Parsing PEP 440 version specifiers.

mod parse;

use crate::scheme::{LocalVersion, PublicVersion};
use thiserror::Error;

/// A comparison clause.
#[derive(Copy, Clone, Debug)]
pub enum Comparison {
    /// `<`
    Less,
    /// `<=`
    LessEqual,
    /// `>`
    Greater,
    /// `>=`
    GreaterEqual,
}

impl std::fmt::Display for Comparison {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Self::Less => "<",
            Self::LessEqual => "<=",
            Self::Greater => ">",
            Self::GreaterEqual => ">=",
        };
        write!(f, "{}", s)
    }
}

/// A compatible version.
///
/// Compatible versions are public versions, but must have at least two release components.
#[derive(Clone, Debug)]
pub struct CompatibleVersion(PublicVersion);

impl CompatibleVersion {
    /// Converts a public version to a compatible version, or returns the original if it has only
    /// one release component.
    pub fn from_public_version(version: PublicVersion) -> Result<Self, PublicVersion> {
        if version.release.len() > 1 {
            Ok(Self(version))
        } else {
            Err(version)
        }
    }

    /// Converts to a public version.
    pub fn into_public_version(self) -> PublicVersion {
        self.0
    }

    /// Converts to a public version.
    pub fn as_public_version(&self) -> &PublicVersion {
        &self.0
    }
}

impl std::fmt::Display for CompatibleVersion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A wildcard version, such as `1.*`
#[derive(Clone, Debug)]
pub struct WildcardVersion(PublicVersion);

impl WildcardVersion {
    /// Converts a public version to a compatible version, or returns the original if it's a
    /// development release.
    pub fn from_public_version(version: PublicVersion) -> Result<Self, PublicVersion> {
        if version.dev.is_none() {
            Ok(Self(version))
        } else {
            Err(version)
        }
    }

    /// Converts to a public version.
    pub fn into_public_version(self) -> PublicVersion {
        self.0
    }

    /// Converts to a public version.
    pub fn as_public_version(&self) -> &PublicVersion {
        &self.0
    }
}

impl std::fmt::Display for WildcardVersion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.*", self.0)
    }
}

/// A PEP 440 version specifier.
#[derive(Clone, Debug)]
pub enum Specifier {
    /// A compatible version, such as `~=1.2`.
    Compatible(CompatibleVersion),
    /// A comparison, such as `<1.2` or `>=3`.
    Comparison(Comparison, PublicVersion),
    /// An exact version, such as `==1.0+foo`.
    Exact(LocalVersion),
    /// An exact exclusion, such as `!=1.0+foo`.
    ExactExclude(LocalVersion),
    /// A wildcard version, such as `==1.*`.
    Wildcard(WildcardVersion),
    /// A wildcard exclusion, such as `!=1.*`.
    WildcardExclude(WildcardVersion),
}

impl Specifier {
    /// Parse a version specifier.
    pub fn parse(s: &str) -> Result<Self, Error> {
        parse::parse_specifier(s)
    }
}

impl std::str::FromStr for Specifier {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}

impl std::fmt::Display for Specifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Compatible(ver) => write!(f, "~={}", ver),
            Self::Comparison(comp, ver) => write!(f, "{}{}", comp, ver),
            Self::Exact(ver) => write!(f, "=={}", ver),
            Self::ExactExclude(ver) => write!(f, "!={}", ver),
            Self::Wildcard(ver) => write!(f, "=={}", ver),
            Self::WildcardExclude(ver) => write!(f, "!={}", ver),
        }
    }
}

/// A set of comma-separated specifiers.
pub struct SpecifierSet(pub Vec<Specifier>);

impl SpecifierSet {
    /// Parse a specifier set.
    pub fn parse(s: &str) -> Result<Self, Error> {
        s.split(',')
            .map(Specifier::parse)
            .collect::<Result<Vec<_>, _>>()
            .map(Self)
    }
}

impl std::str::FromStr for SpecifierSet {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}

impl std::fmt::Display for SpecifierSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut specifiers = self.0.iter();
        if let Some(s) = specifiers.next() {
            write!(f, "{}", s)?;
        }
        for s in specifiers {
            write!(f, ",{}", s)?;
        }
        Ok(())
    }
}

/// A specifier parsing error.
#[derive(Error, Clone, Debug)]
pub enum Error {
    #[error("unexpected value when parsing specifier: {0}")]
    Unexpected(String),
    #[error("compatible version must have at least two release components: {0}")]
    Compatible(PublicVersion),
    #[error("wildcard versions may not be development releases: {0}.*")]
    Wildcard(PublicVersion),
}

/*
#[cfg(test)]
mod test {
    use crate::{Specifier, LocalVersion};

    macro_rules! specifier {
        { $s:literal } => { Specifier::parse($s).unwrap() }
    }

    macro_rules! version {
        { $v:literal } => { LocalVersion::parse($v).unwrap() }
    }

    /// Copied from PEP 440
    #[test]
    fn version_matching() {
        {
        let version = version!("1.1.post1");

        assert!(!specifier!("== 1.1").matches(&version));
        assert!(specifier!("== 1.1.post1").matches(&version));
        assert!(specifier!("== 1.1.*").matches(&version));
        }

        {
        let version = version!("1.1a1");

        assert!(!specifier!("== 1.1").matches(&version));
        assert!(specifier!("== 1.1a1").matches(&version));
        assert!(specifier!("== 1.1.*").matches(&version));
        }

        {
        let version = version!("1.1");

        assert!(specifier!("== 1.1").matches(&version));
        assert!(specifier!("== 1.1.0").matches(&version));
        assert!(!specifier!("== 1.1.dev1").matches(&version));
        assert!(!specifier!("== 1.1a1").matches(&version));
        assert!(!specifier!("== 1.1.post1").matches(&version));
        assert!(specifier!("== 1.1.*").matches(&version));
        }
    }

    /// Copied from PEP 440
    #[test]
    fn version_exclusion() {
        let version = version!("1.1.post1");
        assert!(specifier!("!= 1.1").matches(&version));
        assert!(!specifier!("!= 1.1.post1").matches(&version));
        assert!(!specifier!("!= 1.1.*").matches(&version));
    }

    /// Copied from PEP 440
    #[test]
    fn exclusive_ordered_comparison() {
        assert!(specifier!(">1.7").matches(&version!("1.7.1")));
        assert!(!specifier!(">1.7").matches(&version!("1.7.0.post1")));
        assert!(specifier!(">1.7.post2").matches(&version!("1.7.1")));
        assert!(specifier!(">1.7.post2").matches(&version!("1.7.0.post3")));
        assert!(!specifier!(">1.7.post2").matches(&version!("1.7.0")));
    }

    #[test]
    fn more_wildcard_tests() {
        assert!(specifier!("== 1.0.post1.*").matches(&version!("1.0.post1.dev0")));
        assert!(specifier!("== 1.0rc0.*").matches(&version!("1.0rc0")));
        assert!(specifier!("== 1.0rc0.*").matches(&version!("1.0rc0.dev0")));
        assert!(specifier!("== 1.0rc0.*").matches(&version!("1.0rc0.post0")));
        assert!(specifier!("== 1.0rc0.*").matches(&version!("1.0rc0.post0.dev0")));
        assert!(!specifier!("== 1.0rc0.*").matches(&version!("1.1rc0.dev0")));
        assert!(!specifier!("== 1.0rc0.*").matches(&version!("1.0rc1")));
        assert!(specifier!("== 1.0rc0.post0.*").matches(&version!("1.0rc0.post0")));
        assert!(specifier!("== 1.0rc0.post0.*").matches(&version!("1.0rc0.post0.dev0")));
        assert!(!specifier!("== 1.0a1.*").matches(&version!("1.0b1")));
    }
}
*/
