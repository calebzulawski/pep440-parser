//! Parsing PEP 440 version specifiers.

use crate::{Error, Version};

/// A specifier clause type.
#[derive(Copy, Clone, Debug)]
pub enum ClauseType {
    CompatibleRelease,
    Matching,
    Exclusion,
    WildcardMatching,
    WildcardExclusion,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    ArbitraryEquality,
}

/// A PEP 440 version specifier.
pub struct Specifier {
    clause: ClauseType,
    version: Version,
}

impl Specifier {
    /// Parse a version specifier.
    pub fn parse(s: &str) -> Result<Self, Error> {
        use ClauseType::*;

        // Parse
        let s = s.trim();
        let (clause, s) = if let Some(s) = s.strip_prefix("===") {
            (ArbitraryEquality, s)
        } else if let Some(s) = s.strip_prefix("==") {
            if let Some(s) = s.strip_suffix(".*") {
                (WildcardMatching, s)
            } else {
                (Matching, s)
            }
        } else if let Some(s) = s.strip_prefix("!=") {
            if let Some(s) = s.strip_suffix(".*") {
                (WildcardExclusion, s)
            } else {
                (Exclusion, s)
            }
        } else if let Some(s) = s.strip_prefix("~=") {
            (CompatibleRelease, s)
        } else if let Some(s) = s.strip_prefix("<=") {
            (LessEqual, s)
        } else if let Some(s) = s.strip_prefix("<") {
            (Less, s)
        } else if let Some(s) = s.strip_prefix(">=") {
            (GreaterEqual, s)
        } else if let Some(s) = s.strip_prefix(">") {
            (Greater, s)
        } else {
            return Err(Error::message(format!("invalid specifier: {}", s)));
        };
        let version = Version::parse(s)?;

        // Validate
        match clause {
            Matching | Exclusion => {
                if version.local_version().is_none() {
                    return Err(Error::message(format!(
                        "expected PEP 440 version, got: {}",
                        version
                    )));
                }
            }
            CompatibleRelease | Less | LessEqual | Greater | GreaterEqual => {
                let err = || Error::message(format!("expected public version, got: {}", version));
                if !version.local_version().ok_or_else(err)?.label.0.is_empty() {
                    return Err(err());
                }
            }
            WildcardMatching | WildcardExclusion => {
                let err = || Error::message(format!("expected public version, got: {}", version));
                let local_version = version.local_version().ok_or_else(err)?;
                if !local_version.label.0.is_empty() {
                    return Err(err());
                }
                if local_version.version.dev.is_some() {
                    return Err(Error::message(format!(
                        "development release not allowed in prefix match: {}",
                        version
                    )));
                }
            }
            ArbitraryEquality => {}
        }

        Ok(Self { clause, version })
    }

    /// Returns the type of this specifier.
    pub fn clause_type(&self) -> ClauseType {
        self.clause
    }

    /// Returns the version in this specifier.
    pub fn version(&self) -> &Version {
        &self.version
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
        use ClauseType::*;
        match self.clause {
            CompatibleRelease => write!(f, "~= {}", self.version),
            Matching => write!(f, "== {}", self.version),
            Exclusion => write!(f, "!= {}", self.version),
            WildcardMatching => write!(f, "== {}.*", self.version),
            WildcardExclusion => write!(f, "!= {}.*", self.version),
            Less => write!(f, "< {}", self.version),
            LessEqual => write!(f, "<= {}", self.version),
            Greater => write!(f, "> {}", self.version),
            GreaterEqual => write!(f, ">= {}", self.version),
            ArbitraryEquality => write!(f, "=== {}", self.version),
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
