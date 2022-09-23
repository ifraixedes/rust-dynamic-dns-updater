//! Available supported dynamic DNS providers.

pub mod duckdns;
mod error;

pub use error::Error;

use std::net::{Ipv4Addr, Ipv6Addr};

use async_trait::async_trait;

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

/// Each implementation facilitate updating DNS A records for a specific dynamic DNS provider.
#[async_trait]
trait ARecord {
    /// Update the A DNS record for the indicated domains with the optional provided IP V4 and V6.
    /// Implementation must return an `Error::InvalidArguments` when any domain is indicated or any
    /// IP.
    async fn update_record_a(
        &self,
        domains: &[&str],
        ipv4: Option<Ipv4Addr>,
        ipv6: Option<Ipv6Addr>,
    ) -> Result<Response, Error>;
}
