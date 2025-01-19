#![feature(noop_waker)] // Waker::noop

//! Toy Conflict-Driven Clause-Learning (CDCL) SAT solver for learning

mod backtrack;
pub mod benchmark;
mod brute_force;
mod cdcl;
mod dpll;
mod expr;
mod resolution_trace;
mod selector;
mod timeout;

#[cfg(test)]
pub(crate) mod testing;

pub use backtrack::*;
pub use brute_force::*;
pub use cdcl::*;
pub use dpll::*;
pub use expr::*;
pub use resolution_trace::*;
pub use selector::*;
pub use timeout::*;

use std::collections::BTreeSet;

pub type State = BTreeSet<Literal>;

#[macro_export]
macro_rules! state {
    ($($x:expr),*) => {
        {
            let mut s = $crate::State::new();
            $(s.insert($x.into());)*
            s
        }
    };
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Solution {
    /// Find a satisfying assignment
    Sat(State),
    /// Prove unsatisfiability without certificate
    UnSat,
    /// Prove unsatisfiability with resolution trace for DRAT proof
    UnSatWithProof(ResolutionTrace),
}

impl Solution {
    pub fn as_sat(&self) -> Option<&State> {
        match self {
            Solution::Sat(state) => Some(state),
            _ => None,
        }
    }

    pub fn is_sat(&self) -> bool {
        matches!(self, Solution::Sat(..))
    }

    pub fn is_unsat(&self) -> bool {
        matches!(self, Solution::UnSat | Solution::UnSatWithProof(..))
    }
}
