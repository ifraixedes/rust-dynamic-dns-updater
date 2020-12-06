use std::error as stderr;
use std::fmt;

#[derive(Debug)]
pub enum Error {
    /// Represents invalid arguments regarding the business domain.
    ///
    /// `names` has several conventions about its content.
    /// * When a specific parameter is invalid its value is the exact parameter
    ///   name.
    /// * When the function parameter is a list (vector, array, etc.), the
    ///   invalid items can be __optionally__ indicated using square brackets
    ///   (e.g. `l[3,5,7]`).
    /// * When several function parameters are invalid, its values is the
    ///   parameters names wrapped in round brackets (e.g. `(p1,p3)`); it also
    ///   accepts list items (e.g. `(p1, l[2,10], p5)`).
    /// * When all the function parameters are invalid, `<all>` is used.
    ///
    /// `msg` is a human friendly message that explains why the argument(s) are
    /// invalid.
    ///
    /// # Example
    ///
    /// ```
    /// fn positive_non_zero_div_and_mul(a: i64, b: i64, div: i64) Result<i64, Error> {
    ///     if div == 0 {
    ///         return Err(Error::InvalidArguments{
    ///             names: String::from("div"),
    ///             msg: String::from("div cannot be 0"),
    ///         });
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
    InvalidArguments {
        names: String,
        msg: String,
    },

    // Represents an network operation error.
    Network(surf::Error),
}

impl stderr::Error for Error {
    fn source(&self) -> Option<&(dyn stderr::Error + 'static)> {
        match self {
            Error::InvalidArguments { .. } => None,
            Error::Network(err) => Some(err.as_ref()),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Error::InvalidArguments { names, msg } => {
                write!(f, "{} has an invalid value. {}", names, msg)
            }
            Error::Network(err) => write!(f, "network error: {}", err),
        }
    }
}
