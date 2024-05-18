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
    #[arg(short = 'n', long)]
    max_num_variables: Option<usize>,
    #[arg(short = 't', long, default_value = "10")]
    timeout_secs: u64,
}

impl Args {
    fn digests(&self) -> Result<(String, Vec<Digest>)> {
        match (&self.digest, self.max_num_variables) {
            (None, None) => bail!("Either --digest or --max-num-variables must be specified"),
            (Some(_), Some(_)) => {
                bail!("--digest and --max-num-variables cannot be specified together")
            }
            (Some(digest), None) => Ok((digest.clone(), vec![rgbd::Digest::new(digest.parse()?)])),
            (None, Some(max_num_variables)) => Ok((
                format!("n{}", max_num_variables),
                rgbd::get_sizes()?
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
                    .collect(),
            )),
        }
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
