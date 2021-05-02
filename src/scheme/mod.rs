//! Parsing the PEP 440 version scheme.

mod parse;

use thiserror::Error;

/// A version parsing error.
#[derive(Error, Clone, Debug)]
#[error("unexpected value when parsing version: {unexpected}")]
pub struct Error {
    /// The unexpected value.
    unexpected: String,
}

impl Error {
    fn from_nom(e: nom::error::Error<&str>) -> Self {
        Self {
            unexpected: e.input.trim().to_string(),
        }
    }
}

/// Prerelease segment.
#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub enum Pre {
    A(u64),
    B(u64),
    Rc(u64),
}

impl std::fmt::Display for Pre {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Pre::A(n) => write!(f, "a{}", n)?,
            Pre::B(n) => write!(f, "b{}", n)?,
            Pre::Rc(n) => write!(f, "rc{}", n)?,
        }
        Ok(())
    }
}

/// Release segment.
#[derive(Clone, Debug)]
pub struct Release {
    components: Vec<u64>,
}

impl Release {
    /// Create a new release segment.
    ///
    /// Panics if no components are provided.
    pub fn new(components: Vec<u64>) -> Self {
        assert!(
            !components.is_empty(),
            "release must have at least one digit"
        );
        Self { components }
    }

    /// Convert this back into a Vec of components.
    pub fn into_vec(self) -> Vec<u64> {
        self.components
    }
}

impl std::fmt::Display for Release {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self[0])?;
        for component in self.iter().skip(1) {
            write!(f, ".{}", component)?;
        }
        Ok(())
    }
}

impl std::ops::Deref for Release {
    type Target = [u64];
    fn deref(&self) -> &Self::Target {
        &self.components
    }
}

impl std::ops::DerefMut for Release {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.components
    }
}

impl PartialEq for Release {
    fn eq(&self, rhs: &Self) -> bool {
        let len = self.len().max(rhs.len());
        let left = self.iter().copied().chain(std::iter::repeat(0)).take(len);
        let right = rhs.iter().copied().chain(std::iter::repeat(0)).take(len);
        left.eq(right)
    }
}

impl PartialOrd for Release {
    fn partial_cmp(&self, rhs: &Self) -> Option<std::cmp::Ordering> {
        let len = self.len().max(rhs.len());
        let left = self.iter().copied().chain(std::iter::repeat(0)).take(len);
        let right = rhs.iter().copied().chain(std::iter::repeat(0)).take(len);
        Some(left.cmp(right))
    }
}

impl Eq for Release {}

impl Ord for Release {
    fn cmp(&self, rhs: &Self) -> std::cmp::Ordering {
        self.partial_cmp(rhs).unwrap()
    }
}

impl std::hash::Hash for Release {
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        state.write_u64(self[0]);
        for component in self.iter().skip(1).rev().copied() {
            if component != 0 {
                state.write_u64(component);
            }
        }
    }
}

/// An alphanumeric local version label component.
#[derive(Clone, Debug)]
pub struct Alphanumeric(String);

impl Alphanumeric {
    /// Returns the local version label component only if the string contains ASCII alphanumeric
    /// characters, and contains at least one alphabetic character.
    ///
    /// Otherwise, returns the original string.
    pub fn new(s: String) -> Result<Self, String> {
        if s.chars().all(|c| c.is_ascii_alphanumeric())
            && s.chars().any(|c| c.is_ascii_alphabetic())
        {
            Ok(Self(s))
        } else {
            Err(s)
        }
    }
}

impl std::fmt::Display for Alphanumeric {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::ops::Deref for Alphanumeric {
    type Target = str;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl PartialEq for Alphanumeric {
    fn eq(&self, other: &Self) -> bool {
        self.chars()
            .map(|c| c.to_ascii_lowercase())
            .eq(other.chars().map(|c| c.to_ascii_lowercase()))
    }
}

impl PartialOrd for Alphanumeric {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.chars()
            .map(|c| c.to_ascii_lowercase())
            .partial_cmp(other.chars().map(|c| c.to_ascii_lowercase()))
    }
}

impl Eq for Alphanumeric {}

impl Ord for Alphanumeric {
    fn cmp(&self, rhs: &Self) -> std::cmp::Ordering {
        self.partial_cmp(rhs).unwrap()
    }
}

impl std::hash::Hash for Alphanumeric {
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        for c in self.chars() {
            state.write_u32(c.to_ascii_lowercase() as u32);
        }
    }
}

/// A local version label component.
#[derive(Clone, Debug, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub enum LabelComponent {
    Alphanumeric(Alphanumeric),
    Numeric(u64),
}

impl std::fmt::Display for LabelComponent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Alphanumeric(x) => write!(f, "{}", x),
            Self::Numeric(x) => write!(f, "{}", x),
        }
    }
}

/// A local version label.
#[derive(Clone, Debug, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct Label(pub Vec<LabelComponent>);

impl std::fmt::Display for Label {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !self.0.is_empty() {
            write!(f, "{}", self.0[0])?;
            for part in &self.0[1..] {
                write!(f, ".{}", part)?;
            }
        }
        Ok(())
    }
}

/// A PEP 440 public version.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PublicVersion {
    pub epoch: u64,
    pub release: Release,
    pub pre: Option<Pre>,
    pub post: Option<u64>,
    pub dev: Option<u64>,
}

impl PublicVersion {
    /// Parse a version, also returning if it was in the canonical format.
    pub fn check_parse(s: &str) -> Result<(bool, Self), Error> {
        Self::parse_complete(s)
    }

    /// Parse a version, accepting non-canonical input.
    pub fn parse(s: &str) -> Result<Self, Error> {
        Self::check_parse(s).map(|(_, v)| v)
    }

    /// Increment this version to the next largest version.
    pub fn next(mut self) -> Self {
        let inc = |v: &mut u64| {
            *v = v
                .checked_add(1)
                .expect("overflowed trying to increment release number")
        };
        if let Some(dev) = self.dev.as_mut() {
            inc(dev);
        } else if let Some(post) = self.post.as_mut() {
            inc(post);
        } else {
            self.post = Some(0);
        }
        self
    }
}

impl std::str::FromStr for PublicVersion {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}

impl PartialOrd for PublicVersion {
    fn partial_cmp(&self, rhs: &Self) -> Option<std::cmp::Ordering> {
        // Inverts the ordering of an Option, such that `None` is greater than `Some(anything)`
        fn inv<T>(v: Option<T>) -> (bool, Option<T>) {
            if v.is_some() {
                (false, v)
            } else {
                (true, None)
            }
        }

        let base_dev = |v: &Self| v.pre.is_none() && v.post.is_none() && v.dev.is_some();

        // Order the elements using a tuple
        (
            self.epoch,
            &self.release,
            !base_dev(self), // dev base releases are considered earlier than prereleases
            inv(self.pre),
            self.post,
            inv(self.dev),
        )
            .partial_cmp(&(
                rhs.epoch,
                &rhs.release,
                !base_dev(rhs),
                inv(rhs.pre),
                rhs.post,
                inv(rhs.dev),
            ))
    }
}

impl Ord for PublicVersion {
    fn cmp(&self, rhs: &Self) -> std::cmp::Ordering {
        self.partial_cmp(rhs).unwrap()
    }
}

impl std::fmt::Display for PublicVersion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.epoch != 0 {
            write!(f, "{}!", self.epoch)?;
        }
        write!(f, "{}", self.release)?;
        if let Some(pre) = self.pre {
            write!(f, "{}", pre)?;
        }
        if let Some(post) = self.post {
            write!(f, ".post{}", post)?;
        }
        if let Some(dev) = self.dev {
            write!(f, ".dev{}", dev)?;
        }
        Ok(())
    }
}

/// A PEP 440 local version.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LocalVersion {
    pub version: PublicVersion,
    pub label: Label,
}

impl LocalVersion {
    /// Parse a version, also returning if it was in the canonical format.
    pub fn check_parse(s: &str) -> Result<(bool, Self), Error> {
        Self::parse_complete(s)
    }

    /// Parse a version, accepting non-canonical input.
    pub fn parse(s: &str) -> Result<Self, Error> {
        Self::check_parse(s).map(|(_, v)| v)
    }
}

impl std::fmt::Display for LocalVersion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.version)?;
        if !self.label.0.is_empty() {
            write!(f, "+{}", self.label)?;
        }
        Ok(())
    }
}

impl std::str::FromStr for LocalVersion {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}

#[cfg(test)]
mod test {
    use super::LocalVersion;

    /// Example versions copied from PEP 440
    const EXAMPLE: &[&str] = &[
        "1.0.dev456",
        "1.0a1",
        "1.0a2.dev456",
        "1.0a12.dev456",
        "1.0a12",
        "1.0b1.dev456",
        "1.0b2",
        "1.0b2.post345.dev456",
        "1.0b2.post345",
        "1.0rc1.dev456",
        "1.0rc1",
        "1.0",
        "1.0+abc.5",
        "1.0+abc.7",
        "1.0+5",
        "1.0.post456.dev34",
        "1.0.post456",
        "1.1.dev1",
    ];

    #[test]
    fn round_trip() {
        fn assert_round_trip(s: &str) {
            assert_eq!(format!("{}", LocalVersion::parse(s).unwrap()), s);
        }

        // Check examples
        for version in EXAMPLE {
            assert_round_trip(version);
        }

        // Some other versions
        assert_round_trip("5!100.200.123");
        assert_round_trip("1.0.0.0.0.0.0.0.0.0");
        assert_round_trip("1");
        assert_round_trip("1+1");
        assert_round_trip("1+x");
        assert_round_trip("1+aaaa.bbbb.cccc.1234.1234.1234");
    }

    mod normalize {
        use super::*;

        fn assert_normalize(input: &str, expect: &str) {
            assert_eq!(format!("{}", LocalVersion::parse(input).unwrap()), expect);
        }

        #[test]
        fn case_sensitivity() {
            assert_normalize("1A1", "1a1");
            assert_normalize("1B1", "1b1");
            assert_normalize("1RC1", "1rc1");
            assert_normalize("1.DeV1", "1.dev1");
            assert_normalize("1.pOsT1", "1.post1");
        }

        #[test]
        fn integer_normalization() {
            assert_normalize(
                "004!002.000045.123.0030+0010.100.foo010",
                "4!2.45.123.30+10.100.foo010",
            );
        }

        #[test]
        fn pre_release() {
            // Pre-release separators
            assert_normalize("1.1.a1", "1.1a1");
            assert_normalize("1.5-b_3", "1.5b3");
            assert_normalize("1.3_rc.4", "1.3rc4");

            // Pre-release spelling
            assert_normalize("1aLpHa1", "1a1");
            assert_normalize("1beTa4", "1b4");
            assert_normalize("5c3", "5rc3");
            assert_normalize("5C3", "5rc3");
            assert_normalize("77pRe55", "77rc55");
            assert_normalize("12prEvIew34", "12rc34");

            // Implicit pre-release number
            assert_normalize("1.2a", "1.2a0");
            assert_normalize("1.2b", "1.2b0");
            assert_normalize("1.2rc", "1.2rc0");
        }

        #[test]
        fn post_release() {
            // Post release separators
            assert_normalize("1.2-post.4", "1.2.post4");
            assert_normalize("2.3post_5", "2.3.post5");

            // Post release spelling
            assert_normalize("1.2.r4", "1.2.post4");
            assert_normalize("1.2.rev4", "1.2.post4");

            // Implicit post release number
            assert_normalize("1.2.post", "1.2.post0");

            // Implicit post releases
            assert_normalize("1.2-54", "1.2.post54");
        }

        #[test]
        #[should_panic]
        fn bad_implicit_post_release() {
            LocalVersion::parse("1.2-").unwrap();
        }

        #[test]
        fn development_release() {
            // Development release separators
            assert_normalize("1.2dev-5", "1.2.dev5");
            assert_normalize("1.2-dev_5", "1.2.dev5");

            // Implicit develpment release number
            assert_normalize("1.2.dev", "1.2.dev0");
        }

        #[test]
        fn local_version_segments() {
            assert_normalize("1+ubuntu-xenial_18", "1+ubuntu.xenial.18");
        }

        #[test]
        fn preceding_v_character() {
            assert_normalize("v1", "1");
            assert_normalize("v5!5.0rc4", "5!5.0rc4");
        }

        #[test]
        fn leading_and_trailing_whitespace() {
            // 0x0B is \v and 0x0C is \f
            assert_normalize(" \n  \r    1 \t  \x0C  \x0B ", "1");
        }
    }

    #[test]
    fn ordering() {
        let mut versions = EXAMPLE
            .iter()
            .copied()
            .map(LocalVersion::parse)
            .map(Result::unwrap);

        let mut left = versions.next().unwrap();
        for right in versions {
            println!("{} < {}", left, right);
            assert!(left < right);
            left = right;
        }
    }

    #[test]
    fn next() {
        let versions = EXAMPLE
            .iter()
            .copied()
            .map(|s| LocalVersion::parse(s).unwrap().version);

        for version in versions {
            assert!(version <= version.clone().next());
        }
    }
}
