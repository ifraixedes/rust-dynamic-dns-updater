//! Command-line tool entry point.

#![deny(missing_docs)]

use clap::Parser;

mod cli;
mod error;
mod finders;
mod providers;

fn main() {
    let _ = cli::App::parse();
}
