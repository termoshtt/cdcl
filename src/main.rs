use anyhow::{bail, Result};
use cdcl::*;
use clap::Parser;

#[derive(Debug, Parser)]
struct Args {
    algorithm: String,
    digest: String,
}

fn main() -> Result<()> {
    env_logger::init();

    let args = Args::parse();

    let digest = rgbd::Digest::new(args.digest);
    let expr = CNF::from_rgbd(digest.read()?);

    let solution = match args.algorithm.as_str() {
        "brute_force" => brute_force(expr, take_minimal_id),
        _ => bail!("Unknown algorithm: {}", args.algorithm),
    };
    dbg!(solution);

    Ok(())
}
