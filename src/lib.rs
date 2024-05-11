//! Toy Conflict-Driven Clause-Learning (CDCL) SAT solver for learning

mod brute_force;
mod expr;

pub use brute_force::*;
pub use expr::*;

use std::{
    collections::BTreeMap,
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    },
};

pub type State = BTreeMap<usize, bool>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Solution {
    /// Find a satisfying assignment
    Sat(State),
    /// Prove unsatisfiability
    UnSat,
    /// Solver is canceled
    Canceled,
}

impl Solution {
    pub fn as_sat(&self) -> Option<&State> {
        match self {
            Solution::Sat(state) => Some(state),
            _ => None,
        }
    }
}

pub trait Solver {
    fn solve_cancelable(&mut self, expr: CNF, cancel_token: Arc<AtomicBool>) -> Solution;

    fn solve(&mut self, expr: CNF, timeout: std::time::Duration) -> Solution {
        let cancel_token = Arc::new(AtomicBool::new(false));
        let t = cancel_token.clone();
        std::thread::spawn(move || {
            std::thread::sleep(timeout);
            t.store(true, Ordering::Relaxed);
        });
        self.solve_cancelable(expr, cancel_token)
    }
}
