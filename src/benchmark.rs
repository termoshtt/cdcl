use crate::{Solution, Solver, CNF};
use anyhow::Result;
use colored::Colorize;
use rgbd::Digest;
use serde::{Deserialize, Serialize};
use std::{
    ops::Deref,
    time::{Duration, Instant},
};

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Report {
    solver: &'static str,
    timeout: Duration,
    sat: Vec<(String, Duration)>,
    unsat: Vec<(String, Duration)>,
    timed_out: Vec<String>,
}

pub fn benchmark(
    mut solver: impl Solver,
    digests: Vec<Digest>,
    timeout: Duration,
) -> Result<Report> {
    let n = digests.len();
    let mut sat = Vec::new();
    let mut unsat = Vec::new();
    let mut timed_out = Vec::new();

    eprintln!(
        "{:>12} {} instances",
        "Found".bold().magenta(),
        digests.len()
    );
    for (i, digest) in digests.iter().enumerate() {
        let expr = CNF::from_rgbd(digest.read()?);
        eprintln!(
            "{:>12} ({i}/{n}) {} [timeout = {:?}]",
            "Solving".bold().blue(),
            digest.deref(),
            timeout
        );
        let start = Instant::now();
        let solution = solver.solve(expr, timeout);
        let elapsed = start.elapsed();
        match solution {
            Solution::Sat(_) => {
                eprintln!(
                    "{:>12} {} (in {:?})",
                    "SAT".bold().green(),
                    digest.deref(),
                    elapsed
                );
                sat.push((digest.to_string(), elapsed));
            }
            Solution::UnSat => {
                eprintln!(
                    "{:>12} {} (in {:?})",
                    "UNSAT".bold().green(),
                    digest.deref(),
                    elapsed
                );
                unsat.push((digest.to_string(), elapsed));
            }
            Solution::Canceled => {
                eprintln!(
                    "{:>12} {} (in {:?})",
                    "Timeout".bold().yellow(),
                    digest.deref(),
                    elapsed
                );
                timed_out.push(digest.to_string());
            }
        }
    }

    Ok(Report {
        solver: solver.name(),
        timeout,
        sat,
        unsat,
        timed_out,
    })
}
