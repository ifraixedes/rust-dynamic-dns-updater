//! Command-line tool entry point.

#![deny(missing_docs)]

use clap::Parser;

mod cli;
mod cmd;
mod error;
mod finders;
mod providers;

fn main() {
    let app_args = cli::App::parse();

    match app_args.command {
        // TODO: continue here!
        cli::Command::Update { .. } => {}
    }
}
