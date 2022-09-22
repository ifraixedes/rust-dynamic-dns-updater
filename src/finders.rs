//! Available supported IP public finders.

mod error;
pub mod ipify;

pub use error::Error;

use std::net::{Ipv4Addr, Ipv6Addr};

use async_trait::async_trait;

/// Each implementation facilitate to find out the public IP V4 and V6 of the machine using a
/// specific IP public finder service.
#[async_trait]
pub trait PublicIps {
    /// Gets the IP V4 public IP of the machine.
    async fn ipv4<'a>(&self) -> Result<Ipv4Addr, Error<'a>>;

    /// Gets the IP V6 public IP of the machine.
    async fn ipv6<'a>(&self) -> Result<Ipv6Addr, Error<'a>>;

    /// Gets the IPs V4 and V6 public IP of the machine.
    async fn ips<'a>(&self) -> Result<(Ipv4Addr, Ipv6Addr), Error<'a>>;
}
