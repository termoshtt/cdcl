use crate::{Solution, Solver, CNF};
use anyhow::Result;
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

impl Report {
    pub fn name(&self) -> String {
        format!("report_{}", self.solver)
    }
}

pub fn benchmark(
    solver: &mut dyn Solver,
    digests: Vec<Digest>,
    timeout: Duration,
) -> Result<Report> {
    let n = digests.len();
    let mut sat = Vec::new();
    let mut unsat = Vec::new();
    let mut timed_out = Vec::new();

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
                sat.push((digest.to_string(), elapsed));
            }
            Solution::UnSat => {
                log::info!(
                    "Solved ({i}/{n}): {} is UNSAT (in {:?})",
                    digest.deref(),
                    elapsed
                );
                unsat.push((digest.to_string(), elapsed));
            }
            Solution::Canceled => {
                log::info!("Timeout ({i}/{n}): {} (in {:?})", digest.deref(), elapsed);
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
