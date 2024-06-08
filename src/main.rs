use anyhow::{bail, Result};
use cdcl::*;
use clap::Parser;
use rgbd::Digest;
use std::{fs, path::PathBuf, time::Duration};

#[derive(Debug, Parser)]
struct Args {
    algorithm: String,
    #[arg(long)]
    digest: Option<String>,
    #[arg(short = 'v', long)]
    max_num_variables: Option<usize>,
    #[arg(short = 'c', long)]
    max_num_clauses: Option<usize>,
    #[arg(short = 't', long, default_value = "1")]
    timeout_secs: u64,
}

impl Args {
    fn digests(&self) -> Result<(String, Vec<Digest>)> {
        if let Some(digest) = &self.digest {
            return Ok((digest.clone(), vec![rgbd::Digest::new(digest.parse()?)]));
        }
        let (title, f): (_, Box<dyn Fn(rgbd::Size) -> bool>) =
            match (self.max_num_variables, self.max_num_clauses) {
                (Some(max_num_variables), None) => (
                    format!("v{}", max_num_variables),
                    Box::new(move |size| -> bool { size.variables <= max_num_variables }),
                ),
                (None, Some(max_num_clauses)) => (
                    format!("c{}", max_num_clauses),
                    Box::new(move |size| -> bool { size.clauses <= max_num_clauses }),
                ),
                (Some(max_num_variables), Some(max_num_clauses)) => (
                    format!("v{}c{}", max_num_variables, max_num_clauses),
                    Box::new(move |size| -> bool {
                        size.variables <= max_num_variables && size.clauses <= max_num_clauses
                    }),
                ),
                _ => bail!(
                    "One of --digest, --max-num-variables or --max-num-clauses must be specified"
                ),
            };

        Ok((
            title,
            rgbd::get_sizes()?
                .into_iter()
                .filter_map(|(digest, size)| {
                    size.and_then(|size| if f(size) { Some(digest) } else { None })
                })
                .map(rgbd::Digest::new)
                .collect(),
        ))
    }
}

fn main() -> Result<()> {
    env_logger::Builder::from_default_env()
        .filter(None, log::LevelFilter::Info)
        .init();

    let args = Args::parse();
    let mut solver: Box<dyn Solver> = match args.algorithm.as_str() {
        "brute_force" => Box::new(BruteForce {}),
        _ => bail!("Unknown algorithm: {}", args.algorithm),
    };
    let (title, digests) = args.digests()?;

    let report = cdcl::benchmark::benchmark(
        solver.as_mut(),
        digests,
        Duration::from_secs(args.timeout_secs),
    )?;

    let out = PathBuf::from(format!(
        "report_{title}_{}_{}.json",
        args.algorithm,
        std::process::id(),
    ));
    log::info!("Report written to {}", out.display());
    fs::write(&out, serde_json::to_string_pretty(&report)?)?;
    Ok(())
}
