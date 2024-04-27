//! Toy Conflict-Driven Clause-Learning (CDCL) SAT solver for learning

mod brute_force;
mod expr;

pub use brute_force::*;
pub use expr::*;

use std::collections::BTreeMap;

pub type State = BTreeMap<usize, bool>;
