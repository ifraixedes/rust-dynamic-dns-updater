//! Available supported dynamic DNS providers.

pub mod duckdns;
mod error;

pub use error::Error;

#[derive(Debug)]
pub struct Response {
    updated: Option<bool>,
}

impl Response {
    // Tells if the request has updated the DNS configuration or it has left it
    // as it was because the sent values were equal the ones set.
    // A provider may not provide this information in the response, and it isn't
    // common that a provider implementation makes a request for finding out to
    // avoid extra round trips, in that case the information is unknown and None
    // is returned.
    pub fn is_updated(&self) -> Option<bool> {
        self.updated
    }
}
