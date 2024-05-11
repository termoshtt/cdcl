use anyhow::{bail, Result};
use cdcl::*;
use clap::Parser;
use rgbd::Digest;
use std::{ops::Deref, time::Duration};

#[derive(Debug, Parser)]
struct Args {
    algorithm: String,
    #[arg(long)]
    digest: Option<String>,
    #[arg(short = 'n', long)]
    max_num_variables: Option<usize>,
    #[arg(short = 't', long)]
    timeout_secs: Option<u64>,
}

impl Args {
    fn digests(&self) -> Result<Vec<Digest>> {
        match (&self.digest, self.max_num_variables) {
            (None, None) => bail!("Either --digest or --max-num-variables must be specified"),
            (Some(_), Some(_)) => {
                bail!("--digest and --max-num-variables cannot be specified together")
            }
            (Some(digest), None) => Ok(vec![rgbd::Digest::new(digest.to_string())]),
            (None, Some(max_num_variables)) => Ok(rgbd::get_sizes()?
                .into_iter()
                .filter_map(|(digest, size)| {
                    size.and_then(|size| {
                        if size.variables <= max_num_variables {
                            Some(digest)
                        } else {
                            None
                        }
                    })
                })
                .map(rgbd::Digest::new)
                .collect()),
        }
    }
}

fn main() -> Result<()> {
    env_logger::init();

    let args = Args::parse();
    let mut solver: Box<dyn Solver> = match args.algorithm.as_str() {
        "brute_force" => Box::new(BruteForce {}),
        _ => bail!("Unknown algorithm: {}", args.algorithm),
    };
    let digests = args.digests()?;

    eprintln!("Found {} instances", digests.len());
    for digest in digests {
        println!("Reading {}", digest.deref());
        let expr = CNF::from_rgbd(digest.read()?);
        println!("Solving {}", digest.deref());
        let _solution = solver.solve(expr, args.timeout_secs.map(Duration::from_secs));
    }

    Ok(())
}
