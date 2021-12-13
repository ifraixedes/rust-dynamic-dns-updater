//! Defines an error which any "provider" implementation must return.
//! The error type extends the [common error type](crate::error) to provide
//! kinds of errors to their specific domain.

use crate::error::{Error as ErrorCommon, NetworkSide};

use std::error as stderr;
use std::fmt;

use isahc::error::Error as IsahcError;

/// The error type to wrap the errors returned by the [providers and its
/// descendants modules](crate::providers).
#[non_exhaustive]
#[derive(Debug)]
pub enum Error<'a> {
    /// Common error kinds which are shared across all the modules of this
    /// crate.
    Common(ErrorCommon<'a>),
    /// Identifies error returned by the provider.
    Provider(Provider),
}

impl<'a> Error<'a> {
    /// Convenient constructor for creating the appropriated Error from the
    /// Error type of the isahc module.
    pub(super) fn from_isahc(err: IsahcError) -> Self {
        use isahc::error::ErrorKind;

        match err.kind() {
                ErrorKind::BadServerCertificate | ErrorKind::InvalidContentEncoding
                    | ErrorKind::ProtocolViolation =>
                    Error::Provider(Provider::Internal),
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
                // side error when the host name cannot be resolved, hence we
                // don't check if the error is client or server.
                ErrorKind::NameResolution => Error::Common(ErrorCommon::network(err.into(), NetworkSide::Client, false)),
                ErrorKind::BadClientCertificate | ErrorKind::ClientInitialization
                   | ErrorKind::InvalidCredentials | ErrorKind::TlsEngine => {
                       let side = if err.is_client() { NetworkSide::Client } else { NetworkSide::Server };
                       Error::Common(ErrorCommon::network(err.into(), side, false))
                    }
                ErrorKind::InvalidRequest => panic!("BUG: client created an invalid request. {}", err),
                ErrorKind::RequestBodyNotRewindable => panic!(
                    "BUG (please report it): this error was not expected if it happens it has to be managed by this implementation. {}",
                    err),
                ErrorKind::TooManyRedirects => panic!(
                    "BUG (please report it): this provider implementation is outdated. {}",
                    err),
                _ =>  panic!(
                    "BUG (please report it): outdated implementation, isahc dependency has been updated but this implementation has not been updated properly to match the new 'error kinds'. {} ",
                    err),
            }
    }
}

impl<'a> stderr::Error for Error<'a> {
    fn source(&self) -> Option<&(dyn stderr::Error + 'static)> {
        match self {
            Error::Common(c) => c.source(),
            Error::Provider(_) => None,
        }
    }
}

impl<'a> fmt::Display for Error<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Error::Common(c) => c.fmt(f),
            Error::Provider(p) => p.fmt(f),
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
