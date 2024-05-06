use anyhow::Result;
use cdcl::*;
use clap::Parser;

#[derive(Debug, Parser)]
struct Args {
    digest: String,
}

fn main() -> Result<()> {
    env_logger::init();

    let args = Args::parse();

    let digest = rgbd::Digest::new(args.digest);
    let expr = CNF::from_rgbd(digest.read()?);

    let solution = brute_force(expr, take_minimal_id);
    dbg!(solution);

    Ok(())
}
