use anyhow::{bail, Result};
use cdcl::*;
use clap::Parser;
use colored::Colorize;
use rgbd::Digest;
use std::{
    ops::Deref,
    time::{Duration, Instant},
};

#[derive(Debug, Parser)]
struct Args {
    algorithm: String,
    #[arg(long)]
    digest: Option<String>,
    #[arg(short = 'n', long)]
    max_num_variables: Option<usize>,
    #[arg(short = 't', long, default_value = "10")]
    timeout_secs: u64,
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

    let n = digests.len();
    let mut sat = 0;
    let mut unsat = 0;
    let mut timeout = 0;

    eprintln!(
        "{:>12} {} instances",
        "Found".bold().magenta(),
        digests.len()
    );
    for (i, digest) in digests.iter().enumerate() {
        let expr = CNF::from_rgbd(digest.read()?);
        eprintln!(
            "{:>12} ({i}/{n}) {} [timeout = {}s]",
            "Solving".bold().blue(),
            digest.deref(),
            args.timeout_secs
        );
        let start = Instant::now();
        let solution = solver.solve(expr, Duration::from_secs(args.timeout_secs));
        let elapsed = start.elapsed();
        match solution {
            Solution::Sat(_) => {
                eprintln!(
                    "{:>12} {} (in {:?})",
                    "SAT".bold().green(),
                    digest.deref(),
                    elapsed
                );
                sat += 1;
            }
            Solution::UnSat => {
                eprintln!(
                    "{:>12} {} (in {:?})",
                    "UNSAT".bold().green(),
                    digest.deref(),
                    elapsed
                );
                unsat += 1;
            }
            Solution::Canceled => {
                eprintln!(
                    "{:>12} {} (in {:?})",
                    "Timeout".bold().yellow(),
                    digest.deref(),
                    elapsed
                );
                timeout += 1;
            }
        }
    }
    eprintln!(
        "{:>12} {sat}/{n} SAT, {unsat}/{n} UNSAT, {timeout}/{n} Timeout",
        "Summary".bold().magenta(),
    );

    Ok(())
}
