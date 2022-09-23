//! Update command.

use crate::cli;
use crate::finders as finders_impl;
use crate::finders::PublicIps;
use crate::providers as providers_impl;

use std::boxed::Box;
use std::collections::HashMap;
use std::vec::Vec;

use futures::{stream::FuturesUnordered, StreamExt};

pub async fn execute(
    providers_config: cli::Providers,
    finders_selected: Vec<cli::Finder>,
) -> Result<String, String> {
    /*
    let ips_calls = finders_to_use.iter().map(|f| match f {
        cli::Finder::Ipify => {
            let ipify = finders_impl::ipify::Finder::new();
            tokio::spawn(async move { ipify.ips().await })
        }
    });
    */

    // Find the public IP.
    let (ipv4, ipv6) = {
        let mut finders_to_use =
            HashMap::<&cli::Finder, Box<dyn PublicIps>>::with_capacity(finders_selected.len());
        for f in finders_selected.iter() {
            if !finders_to_use.contains_key(f) {
                let fimpl = match f {
                    cli::Finder::Ipify => finders_impl::ipify::Finder::new(),
                };
                finders_to_use.insert(f, Box::new(fimpl));
            }
        }

        let mut ips_calls = FuturesUnordered::new();
        for f in finders_to_use.values() {
            ips_calls.push(f.ips());
        }

        ips_calls
            .next()
            .await
            .expect("one IP finder to resolve")
            .map_err(|e| format!("{}", e))?
    };

    let mut providers = Vec::with_capacity(1);
    if let Some(config) = providers_config.duck_dns {
        providers.push(providers_impl::duckdns::Updater::new(&config.key));
    }

    todo!();
}
