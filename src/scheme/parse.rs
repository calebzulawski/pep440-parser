use super::{Alphanumeric, Error, LabelComponent, LocalVersion, Pre, PublicVersion, Release};
use nom::{
    branch::alt,
    bytes::complete::tag_no_case,
    character::complete::{alphanumeric1, char, digit1, one_of, satisfy},
    combinator::{all_consuming, map_res, opt},
    multi::{many0_count, separated_list0, separated_list1},
    sequence::{delimited, preceded, terminated, tuple},
    Finish, IResult, Parser,
};

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

// parse the local version label segment
fn label(s: &str) -> IResult<&str, Vec<LabelComponent>> {
    opt(preceded(
        char('+'),
        separated_list0(
            one_of(".-_"),
            alt((
                digit.map(LabelComponent::Numeric),
                alphanumeric1
                    .map(|s: &str| LabelComponent::Alphanumeric(Alphanumeric(s.to_string()))),
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

// parse a public version
fn public_version(s: &str) -> IResult<&str, (bool, PublicVersion)> {
    let v = opt(char('v')).map(|x| x.is_none());
    tuple((v, epoch, release, pre, post, dev))
        .map(|(c0, epoch, release, (c1, pre), (c2, post), (c3, dev))| {
            (
                c0 && c1 && c2 && c3,
                PublicVersion {
                    epoch,
                    release,
                    pre,
                    post,
                    dev,
                },
            )
        })
        .parse(s)
}

impl PublicVersion {
    /// Parse implementation.
    pub(crate) fn parse_impl(s: &str) -> IResult<&str, (bool, Self)> {
        delimited(whitespace, public_version, whitespace)(s)
    }

    pub(super) fn parse_complete(s: &str) -> Result<(bool, Self), super::Error> {
        match all_consuming(Self::parse_impl)(s).finish() {
            Err(e) => Err(Error::from_nom(e)),
            Ok((_, r)) => Ok(r),
        }
    }
}

impl LocalVersion {
    /// Parse implementation.
    pub(crate) fn parse_impl(s: &str) -> IResult<&str, (bool, Self)> {
        delimited(whitespace, tuple((public_version, label)), whitespace)
            .map(|((canonical, version), label)| {
                (canonical && label.is_empty(), Self { version, label })
            })
            .parse(s)
    }

    pub(super) fn parse_complete(s: &str) -> Result<(bool, Self), super::Error> {
        match all_consuming(Self::parse_impl)(s).finish() {
            Err(e) => Err(Error::from_nom(e)),
            Ok((_, r)) => Ok(r),
        }
    }
}
