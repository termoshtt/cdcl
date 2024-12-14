#![feature(noop_waker)] // Waker::noop

//! Toy Conflict-Driven Clause-Learning (CDCL) SAT solver for learning

pub mod benchmark;
mod brute_force;
mod cdcl;
mod dpll;
mod expr;
mod selector;
mod timeout;

#[cfg(test)]
pub(crate) mod testing;

pub use brute_force::*;
pub use cdcl::*;
pub use dpll::*;
pub use expr::*;
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
    /// Prove unsatisfiability
    UnSat,
}

impl Solution {
    pub fn as_sat(&self) -> Option<&State> {
        match self {
            Solution::Sat(state) => Some(state),
            _ => None,
        }
    }
}
