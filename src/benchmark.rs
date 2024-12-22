use crate::{Solution, CNF};
use anyhow::Result;
use rgbd::{Digest, SatResult};
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
    solver: String,
    timeout_msecs: u128,
    entries: Vec<Entry>,
    sorted_elapsed_times: Vec<u128>,
}

impl Report {
    pub fn name(&self) -> String {
        format!("report_{}_{}", self.solver, std::process::id())
    }
}

pub fn benchmark(
    solver_name: String,
    solver: impl Fn(CNF, Duration) -> Result<Solution>,
    digests: Vec<Digest>,
    timeout: Duration,
) -> Result<Report> {
    let n = digests.len();
    let answers = rgbd::get_results()?;
    let mut entries = Vec::new();

    for (i, digest) in digests.iter().enumerate() {
        log::trace!("{:<7} ({i}/{n}): {}", "Loading", digest.deref());
        let expr = CNF::from_rgbd(digest.read()?);
        log::trace!("{:<7} ({i}/{n}): {}", "Solving", digest.deref());
        let start = Instant::now();
        let solution = solver(expr, timeout);
        let elapsed = start.elapsed();
        let answer = answers.get(digest.deref());
        match solution {
            Ok(Solution::Sat(_)) => {
                log::info!(
                    "{:<7} ({i}/{n}): {} is SAT (in {:?})",
                    "Solved",
                    digest.deref(),
                    elapsed
                );
                if let Some(SatResult::UnSat) = answers.get(digest.deref()) {
                    log::error!(
                        "Wrong answer for {}: expected {:?}, got {:?}",
                        digest.deref(),
                        answer,
                        solution
                    );
                }
                entries.push(Entry {
                    digest: digest.to_string(),
                    elapsed_msecs: elapsed.as_millis(),
                    result: "SAT".to_string(),
                });
            }
            Ok(Solution::UnSat | Solution::UnSatWithProof(_)) => {
                log::info!(
                    "{:<7} ({i}/{n}): {} is UNSAT (in {:?})",
                    "Solved",
                    digest.deref(),
                    elapsed
                );
                if let Some(SatResult::Sat) = answers.get(digest.deref()) {
                    log::error!(
                        "Wrong answer for {}: expected {:?}, got {:?}",
                        digest.deref(),
                        answer,
                        solution
                    );
                }
                entries.push(Entry {
                    digest: digest.to_string(),
                    elapsed_msecs: elapsed.as_millis(),
                    result: "UNSAT".to_string(),
                });
            }
            Err(_) => {
                log::info!(
                    "{:<7} ({i}/{n}): {} (in {:?})",
                    "Timeout",
                    digest.deref(),
                    elapsed
                );
                entries.push(Entry {
                    digest: digest.to_string(),
                    elapsed_msecs: elapsed.as_millis(),
                    result: "TIMEOUT".to_string(),
                });
            }
        }
    }

    let timeout_msecs = timeout.as_millis();
    let mut sorted_elapsed_times: Vec<u128> = entries
        .iter()
        .filter_map(|e| {
            if e.elapsed_msecs < timeout_msecs {
                Some(e.elapsed_msecs)
            } else {
                None
            }
        })
        .collect();
    sorted_elapsed_times.sort_unstable();

    Ok(Report {
        solver: solver_name,
        timeout_msecs,
        entries,
        sorted_elapsed_times,
    })
}
