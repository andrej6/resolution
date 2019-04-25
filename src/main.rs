extern crate structopt;

use std::path::PathBuf;
use structopt::StructOpt;

use ares::fileparser;

#[derive(Debug, StructOpt)]
#[structopt(
    name = "ares",
    about = "A resolution verifier for propositional logic."
)]
struct AResArgs {
    /// Input file.
    #[structopt(parse(from_os_str))]
    filename: PathBuf,
}

fn main() {
    let AResArgs { filename } = AResArgs::from_args();
    match fileparser::get_clauses(&filename) {
        Err(e) => eprintln!("Error reading file: {}", e),
        Ok(graph) => match graph.verify_correct() {
            Ok(()) => println!("Looks good!"),
            Err(e) => println!("{}", e),
        },
    }
}
