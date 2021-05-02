use super::{Comparison, CompatibleVersion, Error, Specifier, WildcardVersion};
use crate::scheme::{LocalVersion, PublicVersion};
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::satisfy,
    combinator::{all_consuming, map_res},
    error::{ErrorKind, FromExternalError, ParseError},
    multi::many0_count,
    sequence::{preceded, terminated, tuple},
    Finish, IResult, Parser,
};

struct ErrorImpl(Error);

impl ParseError<&str> for ErrorImpl {
    fn from_error_kind(input: &str, _: ErrorKind) -> Self {
        Self(Error::Unexpected(input.trim().to_string()))
    }

    fn append(_: &str, _: ErrorKind, other: Self) -> Self {
        other
    }
}

impl FromExternalError<&str, Self> for ErrorImpl {
    fn from_external_error(_: &str, _: ErrorKind, e: Self) -> Self {
        e
    }
}

fn err_convert<O>(
    mut f: impl for<'a> Parser<&'a str, O, nom::error::Error<&'a str>>,
) -> impl FnMut(&str) -> IResult<&str, O, ErrorImpl> {
    move |s| {
        f.parse(s)
            .map_err(|e| e.map(|e| ErrorImpl(Error::Unexpected(e.input.trim().to_string()))))
    }
}

fn public_version(s: &str) -> IResult<&str, PublicVersion, ErrorImpl> {
    err_convert(PublicVersion::parse_impl)
        .map(|(_, v)| v)
        .parse(s)
}

fn local_version(s: &str) -> IResult<&str, LocalVersion, ErrorImpl> {
    err_convert(LocalVersion::parse_impl)
        .map(|(_, v)| v)
        .parse(s)
}

/// Parse a compatible version specifier.
fn compatible(s: &str) -> IResult<&str, Specifier, ErrorImpl> {
    map_res(preceded(tag("~="), public_version), |v| {
        Ok(Specifier::Compatible(
            CompatibleVersion::from_public_version(v)
                .map_err(|v| ErrorImpl(Error::Compatible(v)))?,
        ))
    })(s)
}

/// Parse a comparison specifier.
fn comparison(s: &str) -> IResult<&str, Specifier, ErrorImpl> {
    tuple((
        alt((tag("<="), tag(">="), tag("<"), tag(">"))),
        public_version,
    ))
    .map(|(comp, ver)| {
        let comp = match comp {
            "<" => Comparison::Less,
            "<=" => Comparison::LessEqual,
            ">" => Comparison::Greater,
            ">=" => Comparison::GreaterEqual,
            _ => unimplemented!(),
        };
        Specifier::Comparison(comp, ver)
    })
    .parse(s)
}

/// Parse a wildcard specifier.
fn wildcard(s: &str) -> IResult<&str, Specifier, ErrorImpl> {
    map_res(
        tuple((
            alt((tag("=="), tag("!="))),
            terminated(public_version, tag(".*")),
        )),
        |(clause, ver)| {
            let ver = WildcardVersion::from_public_version(ver)
                .map_err(|ver| ErrorImpl(Error::Wildcard(ver)))?;
            Ok(match clause {
                "==" => Specifier::Wildcard(ver),
                "!=" => Specifier::WildcardExclude(ver),
                _ => unimplemented!(),
            })
        },
    )(s)
}

/// Parse an exact specifier.
fn exact(s: &str) -> IResult<&str, Specifier, ErrorImpl> {
    tuple((alt((tag("=="), tag("!="))), local_version))
        .map(|(clause, ver)| match clause {
            "==" => Specifier::Exact(ver),
            "!=" => Specifier::ExactExclude(ver),
            _ => unimplemented!(),
        })
        .parse(s)
}

fn whitespace(s: &str) -> IResult<&str, (), ErrorImpl> {
    many0_count(satisfy(|c| c.is_whitespace()))
        .map(std::mem::drop)
        .parse(s)
}

pub(super) fn parse_specifier(s: &str) -> Result<Specifier, Error> {
    all_consuming(preceded(
        whitespace,
        alt((compatible, comparison, wildcard, exact)),
    ))(s)
    .finish()
    .map(|(_, s)| s)
    .map_err(|e| e.0)
}
