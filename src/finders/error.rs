//! Defines an error which any "finders" implementation must return.
//! The error type extends the [common error type](crate::error) to provide
//! kinds of errors to their specific domain.

use crate::error::{Error as ErrorCommon, ExternalService, NetworkSide};

use std::error as stderr;
use std::fmt;

use isahc::error::Error as IsahcError;

/// The error type to wrap the errors returned by the [finders and its
/// descendants modules](crate::finders).
#[non_exhaustive]
#[derive(Debug)]
pub enum Error {
    /// Common error kinds which are shared across all the modules of this
    /// crate.
    Common(ErrorCommon),
    /// Identifies error returned by the finder.
    Finder(ExternalService),
}

impl Error {
    /// Convenient constructor for creating the appropriated Error from the
    /// Error type of the isahc module.
    pub(super) fn from_isahc(err: IsahcError) -> Self {
        use isahc::error::ErrorKind;

        match err.kind() {
                ErrorKind::BadServerCertificate | ErrorKind::InvalidContentEncoding
                    | ErrorKind::ProtocolViolation =>
                    Error::Finder(ExternalService::Internal{reason: err.to_string()}),
                ErrorKind::ConnectionFailed | ErrorKind::Timeout => {
                    let side = if err.is_client() { NetworkSide::Client } else { NetworkSide::Server };
                    Error::Common(ErrorCommon::network(err.into(), side, true))
                }
                ErrorKind::Io => {
                    if err.is_client() {
                        Error::Common(ErrorCommon::network(err.into(), NetworkSide::Client , false))
                    } else {
                        Error::Common(ErrorCommon::network(err.into(), NetworkSide::Server , true))
                    }
                }
                // NameResolution error is returned indicating that's a server
                // side error when the host name cannot be resolved, but we
                // don't consider it that should be a server side error, hence
                // we always indicate that's a client side error.
                ErrorKind::NameResolution => Error::Common(ErrorCommon::network(err.into(), NetworkSide::Client, false)),
                ErrorKind::BadClientCertificate | ErrorKind::ClientInitialization
                   | ErrorKind::InvalidCredentials | ErrorKind::TlsEngine => {
                       let side = if err.is_client() { NetworkSide::Client } else { NetworkSide::Server };
                       Error::Common(ErrorCommon::network(err.into(), side, false))
                    }
                ErrorKind::InvalidRequest => panic!("BUG: client created an invalid request. {}", err),
                ErrorKind::RequestBodyNotRewindable => panic!(
                    "BUG (please report it): this error should not happen if the implementation is correct. {}",
                    err),
                ErrorKind::TooManyRedirects => panic!(
                    "BUG (please report it): this implementation is outdated, the external service has changed its public API. {}",
                    err),
                _ =>  panic!(
                    "BUG (please report it): outdated implementation, isahc dependency has been updated but this implementation has not been updated properly to match the new 'error kinds'. {} ",
                    err),
            }
    }
}

impl stderr::Error for Error {
    fn source(&self) -> Option<&(dyn stderr::Error + 'static)> {
        match self {
            Error::Common(c) => c.source(),
            Error::Finder(_) => None,
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Error::Common(c) => c.fmt(f),
            Error::Finder(es) => es.fmt(f),
        }
    }
}
