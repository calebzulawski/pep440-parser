//! Parsing the PEP 440 version scheme.

use crate::Error;
use nom::{
    branch::alt,
    bytes::complete::tag_no_case,
    character::complete::{alphanumeric1, char, digit1, one_of, satisfy},
    combinator::{all_consuming, map_res, opt},
    multi::{many0_count, separated_list0, separated_list1},
    sequence::{preceded, terminated, tuple},
    Finish, IResult, Parser,
};

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

    /// Convert this back into a Vec of components
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

/// An alphanumeric local version component.
#[derive(Clone, Debug)]
pub struct Alphanumeric(String);

impl Alphanumeric {
    /// Returns the local version component only if the string contains ASCII alphanumeric
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

/// A local version component.
#[derive(Clone, Debug, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub enum Local {
    Alphanumeric(Alphanumeric),
    Numeric(u64),
}

impl std::fmt::Display for Local {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Alphanumeric(x) => write!(f, "{}", x),
            Self::Numeric(x) => write!(f, "{}", x),
        }
    }
}

/// A PEP 440 version.
///
/// `Display`ing this type renders the normalized version.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Version {
    pub epoch: u64,
    pub release: Release,
    pub pre: Option<Pre>,
    pub post: Option<u64>,
    pub dev: Option<u64>,
    pub local: Vec<Local>,
}

impl Version {
    /// Parse a version, also returning if it was in the canonical format.
    pub fn check_parse(s: &str) -> Result<(bool, Self), Error> {
        match all_consuming(version)(s).finish() {
            Err(nom::error::Error { input, code }) => Err(nom::error::Error {
                input: input.to_string(),
                code,
            }),
            Ok((_, r)) => Ok(r),
        }
    }

    /// Parse a version, accepting non-canonical input.
    pub fn parse(s: &str) -> Result<Self, Error> {
        Self::check_parse(s).map(|(_, v)| v)
    }
}

impl PartialOrd for Version {
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
            &self.local,
        )
            .partial_cmp(&(
                rhs.epoch,
                &rhs.release,
                !base_dev(rhs),
                inv(rhs.pre),
                rhs.post,
                inv(rhs.dev),
                &rhs.local,
            ))
    }
}

impl Ord for Version {
    fn cmp(&self, rhs: &Self) -> std::cmp::Ordering {
        self.partial_cmp(rhs).unwrap()
    }
}

impl std::fmt::Display for Version {
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
        if !self.local.is_empty() {
            write!(f, "+{}", self.local[0])?;
            for local in &self.local[1..] {
                write!(f, ".{}", local)?;
            }
        }
        Ok(())
    }
}

impl std::str::FromStr for Version {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}

// parse a string of digits as a u64
fn digit(s: &str) -> IResult<&str, u64> {
    map_res(digit1, str::parse::<u64>)(s)
}

// parse the epoch segment
fn epoch(s: &str) -> IResult<&str, u64> {
    opt(terminated(digit, char('!')))
        .map(|v| v.unwrap_or(0))
        .parse(s)
}

// parse the release segment
fn release(s: &str) -> IResult<&str, Release> {
    separated_list1(char('.'), digit).map(Release::new).parse(s)
}

fn separator(s: &str) -> IResult<&str, Option<char>> {
    opt(one_of(".-_"))(s)
}

// TODO figure out lifetimes to make this a fn instead
// tag: the allowed tags
// sep: the canonical prefix (None for `a0`, Some('.') for `.post0`)
// canonical: the canonical tag
macro_rules! tagged_num {
    { $tag:expr, $sep:expr, $canonical:literal $(,)? } => {
        tuple((separator, $tag, opt(tuple((separator, digit)))))
            .map(|x| {
                if let Some(digit) = x.2 {
                    (x.0 == $sep && digit.0.is_none() && x.1 == $canonical, digit.1)
                } else {
                    (false, 0)
                }
            })
    }
}

// parse the prerelease segment
fn pre(s: &str) -> IResult<&str, (bool, Option<Pre>)> {
    let a = tagged_num!(alt((tag_no_case("alpha"), tag_no_case("a"))), None, "a")
        .map(|x| (x.0, Pre::A(x.1)));
    let b = tagged_num!(alt((tag_no_case("beta"), tag_no_case("b"))), None, "b")
        .map(|x| (x.0, Pre::B(x.1)));
    let rc = tagged_num!(
        alt((
            tag_no_case("rc"),
            tag_no_case("c"),
            tag_no_case("preview"),
            tag_no_case("pre"),
        )),
        None,
        "rc",
    )
    .map(|x| (x.0, Pre::Rc(x.1)));

    opt(alt((a, b, rc)))
        .map(|x| {
            if let Some((canonical, pre)) = x {
                (canonical, Some(pre))
            } else {
                (true, None)
            }
        })
        .parse(s)
}

// parse the postrelease segment
fn post(s: &str) -> IResult<&str, (bool, Option<u64>)> {
    opt(alt((
        tagged_num!(
            alt((tag_no_case("post"), tag_no_case("rev"), tag_no_case("r"))),
            Some('.'),
            "post",
        ),
        // Implicit post releases
        preceded(char('-'), digit).map(|d| (false, d)),
    )))
    .map(|x| {
        if let Some((canonical, pre)) = x {
            (canonical, Some(pre))
        } else {
            (true, None)
        }
    })
    .parse(s)
}

// parse the dev segment
fn dev(s: &str) -> IResult<&str, (bool, Option<u64>)> {
    opt(tagged_num!(tag_no_case("dev"), Some('.'), "dev",))
        .map(|x| {
            if let Some((canonical, pre)) = x {
                (canonical, Some(pre))
            } else {
                (true, None)
            }
        })
        .parse(s)
}

// parse the local segment
fn local(s: &str) -> IResult<&str, Vec<Local>> {
    opt(preceded(
        char('+'),
        separated_list0(
            one_of(".-_"),
            alt((
                digit.map(Local::Numeric),
                alphanumeric1.map(|s: &str| Local::Alphanumeric(Alphanumeric(s.to_string()))),
            )),
        ),
    ))
    .map(|x| x.unwrap_or_else(Vec::new))
    .parse(s)
}

fn whitespace(s: &str) -> IResult<&str, ()> {
    many0_count(satisfy(|c| c.is_whitespace()))
        .map(std::mem::drop)
        .parse(s)
}

// parse a version
fn version(s: &str) -> IResult<&str, (bool, Version)> {
    let v = opt(char('v')).map(|x| x.is_none());
    tuple((
        whitespace, v, epoch, release, pre, post, dev, local, whitespace,
    ))
    .map(
        |(_, c0, epoch, release, (c1, pre), (c2, post), (c3, dev), local, _)| {
            (
                c0 && c1 && c2 && c3 && local.is_empty(),
                Version {
                    epoch,
                    release,
                    pre,
                    post,
                    dev,
                    local,
                },
            )
        },
    )
    .parse(s)
}

#[cfg(test)]
mod test {
    use super::Version;

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
            assert_eq!(format!("{}", Version::parse(s).unwrap()), s);
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
            assert_eq!(format!("{}", Version::parse(input).unwrap()), expect);
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
            Version::parse("1.2-").unwrap();
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
            .map(Version::parse)
            .map(Result::unwrap);

        let mut left = versions.next().unwrap();
        for right in versions {
            println!("{} < {}", left, right);
            assert!(left < right);
            left = right;
        }
    }
}
