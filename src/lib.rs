//! Toy Conflict-Driven Clause-Learning (CDCL) SAT solver for learning

mod brute_force;
mod expr;

pub use brute_force::*;
pub use expr::*;

use std::collections::BTreeMap;

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
