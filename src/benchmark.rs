use crate::{Solution, Solver, CNF};
use anyhow::Result;
use rgbd::Digest;
use serde::{Deserialize, Serialize};
use std::{
    ops::Deref,
    time::{Duration, Instant},
};

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Entry {
    pub digest: String,
    pub elapsed_msecs: u128,
    pub result: String,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Report {
    solver: &'static str,
    timeout_msecs: u128,
    entries: Vec<Entry>,
}

impl Report {
    pub fn name(&self) -> String {
        format!("report_{}_{}", self.solver, std::process::id())
    }
}

pub fn benchmark(
    solver: &mut dyn Solver,
    digests: Vec<Digest>,
    timeout: Duration,
) -> Result<Report> {
    let n = digests.len();
    let mut entries = Vec::new();

    for (i, digest) in digests.iter().enumerate() {
        let expr = CNF::from_rgbd(digest.read()?);
        let start = Instant::now();
        let solution = solver.solve(expr, timeout);
        let elapsed = start.elapsed();
        match solution {
            Solution::Sat(_) => {
                log::info!(
                    "Solved ({i}/{n}): {} is SAT (in {:?})",
                    digest.deref(),
                    elapsed
                );
                entries.push(Entry {
                    digest: digest.to_string(),
                    elapsed_msecs: elapsed.as_millis(),
                    result: "SAT".to_string(),
                });
            }
            Solution::UnSat => {
                log::info!(
                    "Solved ({i}/{n}): {} is UNSAT (in {:?})",
                    digest.deref(),
                    elapsed
                );
                entries.push(Entry {
                    digest: digest.to_string(),
                    elapsed_msecs: elapsed.as_millis(),
                    result: "UNSAT".to_string(),
                });
            }
            Solution::Canceled => {
                log::info!("Timeout ({i}/{n}): {} (in {:?})", digest.deref(), elapsed);
                entries.push(Entry {
                    digest: digest.to_string(),
                    elapsed_msecs: elapsed.as_millis(),
                    result: "TIMEOUT".to_string(),
                });
            }
        }
    }

    Ok(Report {
        solver: solver.name(),
        timeout_msecs: timeout.as_millis(),
        entries,
    })
}
