//! Defines a common error type that exposes kinds of errors that any submodule
//! may return.
//! Every submodule should create a specific error type as a submodule of it to
//! define specific kinds of errors for their specific domain. Even a submodule
//! which doesn't have any specific kinds of errors should create its own error
//! type for having the chance to add new kinds of errors in the future without
//! having to change the functions and methods returns values, which would be
//! breaking changes.

use std::error as stderr;
use std::fmt;

/// Convenient type for making more concise wrapping the standard error trait
/// object into a Box.
pub type BoxError = Box<dyn stderr::Error + Send + Sync>;

/// The error type that expose general kinds of errors that are common to all
/// the modules of this crate.
#[non_exhaustive]
#[derive(Debug)]
pub enum Error<'a> {
    /// Identify unexpected errors which happen because of the state of the
    /// system where the application is running, for example, insufficient
    /// resources, OS failures, etc.
    Internal(Internal<'a>),
    /// Identify errors due to invalid arguments passed to function or methods
    /// or assigned values to configurations.
    InvalidArguments(Args),
    /// Identify errors related with the network produced by the client or
    /// server side and informs to retry or not the operation.
    /// NOTE use an exponential back-off when retrying any operation after
    /// receiving this error indicating to retry it.
    Network(Network),
}

impl<'a> Error<'a> {
    /// Convenient constructor for creating an InvalidArguments Error.
    /// See [`Args`] documentation to know about the convention for the value of
    /// the `names` parameter because this constructor panics if they are
    /// violated.
    pub(crate) fn new_invalid_arguments(names: &str, msg: &str) -> Self {
        Self::InvalidArguments(Args::new(names, msg))
    }

    /// Convenient constructor for creating a Network Error.
    pub(crate) fn new_network(origin: BoxError, side: NetworkSide, should_retry: bool) -> Self {
        Self::Network(Network {
            side,
            should_retry,
            inner: origin,
        })
    }

    /// Convenient constructor for creating an Internal Error.
    pub(crate) fn new_internal(ctx_msg: &'a str, error: BoxError) -> Self {
        Self::Internal(Internal { ctx_msg, error })
    }
}

impl<'a> stderr::Error for Error<'a> {
    fn source(&self) -> Option<&(dyn stderr::Error + 'static)> {
        match self {
            Error::InvalidArguments { .. } => None,
            Error::Internal(i) => i.source(),
            Error::Network(n) => n.source(),
        }
    }
}

impl<'a> fmt::Display for Error<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Error::InvalidArguments(a) => a.fmt(f),
            Error::Internal(i) => i.fmt(f),
            Error::Network(n) => n.fmt(f),
        }
    }
}

/// Represents invalid arguments error regarding the business domain.
///
/// # Example
///
/// ```
/// use storj_uplink_lib::Error;
///
/// fn positive_non_zero_div_and_mul(a: i64, b: i64, div: i64) -> Result<i64, Error> {
///     if div == 0 {
///         return Err(Error::new_invalid_arguments("div", "div cannot be 0"));
///     }
///
///     if (a == 0 && b != 0) || (a != 0 && b == 0) {
///         return Err(Error::new_invalid_arguments(
///             "(a,b)", "a and b can only be 0 if both are 0",
///         ));
///     }
///
///     if (a >= 0 && b >= 0 && div > 0) || (a <= 0 && b <= 0 && div < 0 ) {
///         return Ok((a/div) * (b/div));
///     }
///
///     Err(Error::new_invalid_arguments(
///         "<all>", "all the arguments must be positive or negative, they cannot be mixed",
///     ))
/// }
/// ```
#[derive(Debug)]
pub struct Args {
    /// `names` is one or several parameters names; it has several conventions
    /// for expressing the involved parameters.
    ///
    /// * When a specific parameter is invalid its value is the exact parameter
    ///   name.
    /// * When the parameter is a list (vector, array, etc.), the invalid items
    ///   can be __optionally__ indicated using square brackets (e.g. `l[3,5,7]`).
    /// * when the parameter is struct, the invalid fields or method return
    ///   return values can be __optionally__ indicated using curly brackets
    ///   (e.g invalid field: `person{name}`, invalid method return value:
    ///   `person{full_name()}`, invalid fields/methods:
    ///   `employee{name, position()}`).
    /// * When several parameters are invalid, its value is the parameters names
    ///   wrapped in round brackets (e.g. `(p1,p3)`); it also accepts any of the
    ///   above combination of parameters types
    ///   (e.g. `(p1,l[2,10],person{name})`).
    /// * When all the function parameters are invalid, `<all>` is used.
    ///
    /// For enforcing the conventions across your code base use the
    /// [`Error::new_invalid_arguments`] constructor function.
    pub names: String,
    /// `msg` is a human friendly message that explains why the argument(s) are
    /// invalid.
    pub msg: String,
}

impl Args {
    // TODO: this constructor must enforce the names convention commented in the
    // documentation of this type and panic if they are violated because that
    // means that there is a bug in the code that uses it.
    pub(crate) fn new(names: &str, msg: &str) -> Self {
        Args {
            names: String::from(names),
            msg: String::from(msg),
        }
    }
}

impl fmt::Display for Args {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        // TODO: format the message depending if the arguments are the whole
        // argument, structs fields, lists, etc.
        write!(
            f,
            "{} arguments have invalid values. {}",
            self.names, self.msg
        )
    }
}

#[derive(Debug)]
/// An unexpected error which happens due to the state of the system where the
/// application is running; for example, insufficient resources, OS failure,
/// hardware failure, etc.
pub struct Internal<'a> {
    /// A human friendly message to provide context of the error.
    pub ctx_msg: &'a str,
    /// The received error which cannot be handled by the application and get
    /// wrapped by this instance.
    pub(crate) error: BoxError,
}

impl<'a> stderr::Error for Internal<'a> {
    fn source(&self) -> Option<&(dyn stderr::Error + 'static)> {
        Some(self.error.as_ref())
    }
}

impl<'a> fmt::Display for Internal<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.ctx_msg)
    }
}

/// An error caused by the network when performing a requested operation.
#[derive(Debug)]
pub struct Network {
    pub side: NetworkSide,
    pub should_retry: bool,
    pub(crate) inner: BoxError,
}

impl stderr::Error for Network {
    fn source(&self) -> Option<&(dyn stderr::Error + 'static)> {
        Some(self.inner.as_ref())
    }
}

impl fmt::Display for Network {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let retry = if self.should_retry { "yes" } else { "no" };
        write!(
            f,
            "Network error produced by the {} side (should retry operation: {})",
            self.side, retry,
        )
    }
}

/// Indicates the network side which originated the error.
#[derive(Debug, PartialEq)]
pub enum NetworkSide {
    /// Indicates that the error is in the client side.
    Client,
    /// Indicates that the error is in the server side.
    Server,
}

impl fmt::Display for NetworkSide {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            NetworkSide::Client => write!(f, "client"),
            NetworkSide::Server => write!(f, "server"),
        }
    }
}

#[derive(Debug, PartialEq)]
/// An error returned by the provider when performing a requested operation.
pub enum Provider {
    /// Indicates that the provider has returned an internal error.
    Internal,
    /// Indicates that the provider has returned an errors which isn't currently
    /// specified in its API documentation.
    Unspecified,
}

impl fmt::Display for Provider {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Provider::Internal => write!(f, "service had an internal error"),
            Provider::Unspecified => write!(f, "service reported an unspecified error"),
        }
    }
}
