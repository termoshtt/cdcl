use anyhow::{bail, Result};
use cdcl::*;
use clap::Parser;
use env_logger::{Builder, Env};
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
    #[arg(long)]
    track: Option<String>,
    #[arg(short = 't', long, default_value = "1")]
    timeout_secs: u64,
}

impl Args {
    fn digests(&self) -> Result<(String, Vec<Digest>)> {
        if let Some(track) = &self.track {
            return Ok((track.clone(), rgbd::get_track(track)?));
        }

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
    Builder::from_env(Env::default().filter_or("RUST_LOG", "info")).init();

    let args = Args::parse();
    let name = args.algorithm.clone();
    let solver = match name.as_str() {
        "brute_force" => brute_force,
        "dpll" => dpll,
        "cdcl" => cdcl,
        _ => bail!("Unknown algorithm: {}", name),
    };
    let (title, digests) = args.digests()?;

    let report = cdcl::benchmark::benchmark(
        name.clone(),
        |expr, timeout| todo!(),
        digests,
        Duration::from_secs(args.timeout_secs),
    )?;

    let out = PathBuf::from(format!(
        "report_{title}_{}_{}.json",
        name,
        std::process::id(),
    ));
    log::info!("Report written to {}", out.display());
    fs::write(&out, serde_json::to_string_pretty(&report)?)?;
    Ok(())
}
