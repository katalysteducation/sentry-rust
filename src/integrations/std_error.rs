//! Adds support for `std::error::Error`.
//!
//! **Feature:** `with_std_error`
//!
//! # Example
//!
//! ```no_run
//! # extern crate sentry;
//! # #[derive(Debug)]
//! # struct MyError;
//! # impl std::fmt::Display for MyError {
//! # fn fmt(&self, _: &mut std::fmt::Formatter) -> std::fmt::Result { Ok(()) }
//! # }
//! # impl std::error::Error for MyError {}
//! # fn function_that_might_fail() -> Result<(), MyError> { Ok(()) }
//! use sentry::integrations::std_error::capture_error;
//! # fn test() -> Result<(), MyError> {
//! let result = match function_that_might_fail() {
//!     Ok(result) => result,
//!     Err(err) => {
//!         capture_error(&err);
//!         return Err(err);
//!     }
//! };
//! # Ok(()) }
//! # fn main() { test().unwrap() }

use std::error::Error;

use crate::hub::Hub;
use crate::internals::Uuid;
use crate::protocol::{Event, Exception, Level, Stacktrace};

#[cfg(feature = "with_std_backtrace")]
use crate::backtrace_support::{demangle_symbol, filename, strip_symbol};
#[cfg(feature = "with_std_backtrace")]
use crate::protocol::Frame;
#[cfg(feature = "with_std_backtrace")]
use regex::Regex;
#[cfg(feature = "with_std_backtrace")]
use std::backtrace::BacktraceStatus;

#[cfg(feature = "with_std_backtrace")]
lazy_static::lazy_static! {
    static ref FRAME_RE: Regex = Regex::new(
        r#"(?xm)
        ^
            \s*(?:\d+:)?\s*                      # frame number (missing for inline)

            (?:
                (?P<addr>0x[a-f0-9]+)            # old style address prefix
                \s-\s
            )?

            (?P<symbol>[^\r\n\(]+)               # symbol name

            (?:
                \r?\n
                \s+at\s                          # padded "at" in new line
                (?P<path>[^\r\n]+?)              # path to source file
                (?::(?P<lineno>\d+))?            # optional source line
            )?
        $
    "#
    )
    .unwrap();
}

#[cfg(feature = "with_std_backtrace")]
fn parse_stacktrace(bt: &str) -> Option<Stacktrace> {
    let mut last_address = None;

    let frames = FRAME_RE
        .captures_iter(&bt)
        .map(|captures| {
            let abs_path = captures.name("path").map(|m| m.as_str().to_string());
            let filename = abs_path.as_ref().map(|p| filename(p));
            let real_symbol = captures["symbol"].to_string();
            let symbol = strip_symbol(&real_symbol);
            let function = demangle_symbol(symbol);

            // Obtain the instruction address. A missing address usually indicates an inlined stack
            // frame, in which case the previous address needs to be used.
            last_address = captures
                .name("addr")
                .and_then(|m| m.as_str().parse().ok())
                .or(last_address);

            Frame {
                symbol: if symbol != function {
                    Some(symbol.into())
                } else {
                    None
                },
                function: Some(function),
                instruction_addr: last_address,
                abs_path,
                filename,
                lineno: captures
                    .name("lineno")
                    .map(|x| x.as_str().parse::<u64>().unwrap()),
                ..Default::default()
            }
        })
        .collect();

    Stacktrace::from_frames_reversed(frames)
}

#[cfg(feature = "with_std_backtrace")]
fn capture_stacktrace<E: Error + ?Sized>(e: &E) -> Option<Stacktrace> {
    let bt = e.backtrace()?;

    if bt.status() == BacktraceStatus::Captured {
        let bt = format!("{:#?}", bt);
        parse_stacktrace(&bt)
    } else {
        None
    }
}

#[cfg(not(feature = "with_std_backtrace"))]
fn capture_stacktrace<E: Error + ?Sized>(_: &E) -> Option<Stacktrace> {
    None
}

fn parse_type_name(tn: &str) -> (Option<String>, String) {
    // While standard library guarantees little about format of
    // std::any::type_name(), we can assume it contains the type's name and
    // possibly its module path and generic parameters, likely formatted as
    // path::Name<Generics>.

    let mut first_bracket = tn.len();

    // If tn ends with a '>' then it's likely it a generic type. In this case we
    // don't know which '::' is the last '::' separating module path from type's
    // name since there may be '::' in generics, such as in
    // `Option<std::string::String>`. This fragment tries to find the opening
    // bracket of the generic block.
    if tn.ends_with('>') {
        // Number of opened brackets.
        let mut count = 0;
        let mut end = tn.len();

        while let Some(inx) = tn[..end].rfind(&['<', '>'] as &[char]) {
            end = inx;
            let chr = tn[inx..].chars().next().unwrap();

            // There are more opening brackets than closing brackets.
            if chr == '<' && count == 0 {
                break;
            }

            // Found the first opening bracket.
            if chr == '<' && count == 1 {
                first_bracket = inx;
                break;
            }

            if chr == '<' {
                // Found an opening bracket.
                count -= 1;
            } else {
                // Found a closing bracket.
                count += 1;
            }
        }
    }

    // At this point first_bracket point to either the end of tn, or to the
    // first character of what we believe is a generic parameter block. We can
    // expect then, that the last '::' before first_bracket separates module
    // path from type name.

    match tn[..first_bracket].rfind("::") {
        // ::Name
        Some(0) => (None, tn[2..].to_string()),
        // path::Name
        Some(inx) => (Some(tn[..inx].to_string()), tn[inx + 2..].to_string()),
        // Name
        None => (None, tn.to_string()),
    }
}

fn error_typename<E: ?Sized>() -> (Option<String>, String) {
    parse_type_name(std::any::type_name::<E>())
}

/// This converts a single error instance into an exception.
///
/// This is typically not very useful as the `event_from_error` method will
/// assemble an entire event with all the causes of an error, however for
/// certain more complex situations where errors are contained within a non
/// error error type that might also carry useful information it can be useful
/// to call this method instead.
pub fn exception_from_single_error<E: Error + ?Sized>(e: &E) -> Exception {
    let (module, ty) = error_typename::<E>();
    Exception {
        ty,
        module,
        value: Some(e.to_string()),
        stacktrace: capture_stacktrace(e),
        ..Default::default()
    }
}

/// Helper function to create an event from a `std::error::Error`.
pub fn event_from_error<E: Error + ?Sized>(err: &E) -> Event<'static> {
    let mut exceptions = vec![exception_from_single_error(err)];

    let mut ptr: Option<&dyn Error> = None;
    while let Some(source) = ptr.map(Error::source).unwrap_or_else(|| err.source()) {
        exceptions.push(exception_from_single_error(source));
        ptr = Some(source);
    }

    exceptions.reverse();
    Event {
        exception: exceptions.into(),
        level: Level::Error,
        ..Default::default()
    }
}

/// Captures a `std::error::Error`.
///
/// This dispatches to the current hub.
pub fn capture_error<E: Error + ?Sized>(err: &E) -> Uuid {
    Hub::with_active(|hub| hub.capture_error(err))
}

/// Hub extension methods for working with errors.
pub trait ErrorHubExt {
    /// Captures a `std::error::Error`.
    fn capture_error<E: Error + ?Sized>(&self, err: &E) -> Uuid;
}

impl ErrorHubExt for Hub {
    fn capture_error<E: Error + ?Sized>(&self, err: &E) -> Uuid {
        self.capture_event(event_from_error(err))
    }
}

#[test]
fn test_parse_typename() {
    assert_eq!(parse_type_name("JustName"), (None, "JustName".into()));
    assert_eq!(
        parse_type_name("With<Generics>"),
        (None, "With<Generics>".into()),
    );
    assert_eq!(
        parse_type_name("with::module::Path"),
        (Some("with::module".into()), "Path".into()),
    );
    assert_eq!(
        parse_type_name("with::module::Path<and::Generics>"),
        (Some("with::module".into()), "Path<and::Generics>".into()),
    );
}

#[cfg(feature = "with_std_backtrace")]
#[test]
fn test_parse_stacktrace() {
    use crate::protocol::Addr;

    let backtrace = r#"
   2:     0x56555555750e - <some::crate::Error as core::convert::From<F>>::from::h1fff197f562ea277
                               at /root/.cargo/registry/src/github.com-1ecc6299db9ec823/some-crate/src/error.rs:42
                           rust::inline2::hecf76d76861f1b7b
                               at src/main.rs:7
                           rust::not_inline::h18514b19761d3353
                               at src/main.rs:11
                           main::h8d0e29cc46a13d38
                               at src/main.rs:16
   7:     0x565555557638 - main
"#;

    let stacktrace = parse_stacktrace(backtrace).expect("stacktrace");
    assert_eq!(stacktrace.frames.len(), 5);

    assert_eq!(stacktrace.frames[0].function, Some("main".into()));
    assert_eq!(
        stacktrace.frames[0].instruction_addr,
        Some(Addr(0x5655_5555_7638))
    );

    // Inlined frame, inherits address from parent
    assert_eq!(
        stacktrace.frames[2].function,
        Some("rust::not_inline".into())
    );
    assert_eq!(
        stacktrace.frames[2].instruction_addr,
        Some(Addr(0x5655_5555_750e))
    );
}
