use std::error as stderr;
use std::fmt;

#[derive(Debug)]
pub enum Error<'a> {
    InvalidArguments(Args),
    /// Represents an network operation error.
    /// The associated error value is the one obtained from the underlying
    /// library used for accessing to the network.
    /// The second element, the bool value indicates, when true, that the client
    /// should retry the request after awhile (probably using some exponential
    /// back off technique), otherwise it should not until something (depending
    /// of the error) gets fixed. The client should assess how many times to
    /// retry depending of the specific error provided by the underlying crate.
    Network(&'a (dyn stderr::Error + 'static), bool),
    Provider(Provider),
}

impl<'a> Error<'a> {
    /// Convenient for creating an InvalidArguments Error.
    /// See [`Args`] documentation to know about the convention for the value of
    /// the `names` parameter because this constructor panics if they are
    /// violated.
    pub fn new_invalid_arguments(names: &str, msg: &str) -> Self {
        Self::InvalidArguments(Args::new(names, msg))
    }
}

impl<'a> stderr::Error for Error<'a> {
    fn source(&self) -> Option<&(dyn stderr::Error + 'static)> {
        match self {
            Error::InvalidArguments { .. } => None,
            Error::Network(op_err, _) => Some(*op_err),
            Error::Provider(_) => None,
        }
    }
}

impl<'a> fmt::Display for Error<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Error::InvalidArguments(args) => {
                write!(f, "{}", args)
            }
            Error::Network(err, retry) => {
                if *retry {
                    write!(f, "network error (retry operation): {}", err)
                } else {
                    write!(f, "network error (DO NOT retry operation): {}", err)
                }
            }
            Error::Provider(p) => write!(f, "{}", p),
        }
    }
}

#[derive(Debug)]
/// Represents invalid arguments regarding the business domain.
///
/// # Example
///
/// ```
/// fn positive_non_zero_div_and_mul(a: i64, b: i64, div: i64) Result<i64, Error> {
///     if div == 0 {
///         return Err(Error::new_invalid_arguments("div", "div cannot be 0"));
///     }
///
///     if (a == 0 && b != 0) || (a != 0 && b == 0) {
///         return Err(Error::InvalidArguments{
///             names: String::from("(a,b)"),
///             msg: String::from("a and b can only be 0 if both are 0"),
///         });
///     }
///
///     if (a >= 0 && b >= 0 && div > 0) || (a <= 0 && b <= 0 && div < 0 ) {
///         return Ok((a/div) * (b/div));
///     }
///
///     Err(Error::InvalidArguments{
///         names:String::from("<all>"),
///         msg: "all the arguments must be positive or negative, they cannot be mixed",
///     })
/// }
///
/// assert_eq!(positive_non_zero_div_and_mul(1, 3, 1), Ok(3));
/// ```
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
    /// * When several parameters are invalid, its values is the parameters
    ///   names wrapped in round brackets (e.g. `(p1,p3)`); it also accepts any
    ///   above combination of parameters types
    ///   (e.g. `(p1, l[2,10], person{name})`).
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
    fn new(names: &str, msg: &str) -> Self {
        Args {
            names: String::from(names),
            msg: String::from(msg),
        }
    }
}

impl fmt::Display for Args {
    // TODO: implement a specific message depending on names
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} argurments have invalid values. {}",
            self.names, self.msg
        )
    }
}

#[derive(Debug, PartialEq)]
pub enum Provider {
    Internal,
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
