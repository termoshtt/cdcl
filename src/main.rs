use anyhow::{bail, Result};
use cdcl::*;
use clap::Parser;
use std::time::Duration;

#[derive(Debug, Parser)]
struct Args {
    algorithm: String,
    digest: String,
    #[clap(long)]
    timeout_secs: Option<u64>,
}

fn main() -> Result<()> {
    env_logger::init();
    let args = Args::parse();

    let mut solver: Box<dyn Solver> = match args.algorithm.as_str() {
        "brute_force" => Box::new(BruteForce {}),
        _ => bail!("Unknown algorithm: {}", args.algorithm),
    };

    let digest = rgbd::Digest::new(args.digest);
    let expr = CNF::from_rgbd(digest.read()?);

    let _solution = solver.solve(expr, args.timeout_secs.map(Duration::from_secs));
    Ok(())
}
