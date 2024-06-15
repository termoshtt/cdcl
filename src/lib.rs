//! Toy Conflict-Driven Clause-Learning (CDCL) SAT solver for learning

pub mod benchmark;
mod brute_force;
mod dpll;
mod expr;
mod selector;

#[cfg(test)]
pub(crate) mod testing;

pub use brute_force::*;
pub use dpll::*;
pub use expr::*;
pub use selector::*;

use std::{
    collections::BTreeMap,
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    },
    time::Duration,
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

#[derive(Clone)]
pub struct CancelToken(Arc<AtomicBool>);

impl Default for CancelToken {
    fn default() -> Self {
        Self::new()
    }
}

impl CancelToken {
    pub fn new() -> Self {
        Self(Arc::new(AtomicBool::new(false)))
    }

    pub fn cancel(&self) {
        self.0.store(true, Ordering::Relaxed);
    }

    pub fn is_canceled(&self) -> bool {
        self.0.load(Ordering::Relaxed)
    }
}

pub trait Solver {
    fn name(&self) -> &'static str;

    fn solve_cancelable(&mut self, expr: CNF, cancel_token: CancelToken) -> Solution;

    fn solve(&mut self, expr: CNF, timeout: Duration) -> Solution {
        let cancel_token = CancelToken::new();
        let t = cancel_token.clone();
        std::thread::spawn(move || {
            std::thread::sleep(timeout);
            t.cancel();
        });
        self.solve_cancelable(expr, cancel_token)
    }
}
