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

use std::{
    collections::BTreeSet,
    fmt,
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    },
    time::Duration,
};

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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Canceled;

impl fmt::Display for Canceled {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Canceled")
    }
}

impl std::error::Error for Canceled {}

pub type Cancelable<T> = Result<T, Canceled>;

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

    pub fn is_canceled(&self) -> Cancelable<()> {
        if self.0.load(Ordering::Relaxed) {
            Err(Canceled)
        } else {
            Ok(())
        }
    }
}

pub type CancelableSolver = Box<dyn Fn(CNF, CancelToken) -> Cancelable<Solution>>;
pub type TimeoutSolver = Box<dyn Fn(CNF, Duration) -> Cancelable<Solution>>;

pub fn as_timeout_solver(
    cancelable: impl Fn(CNF, CancelToken) -> Cancelable<Solution> + 'static,
) -> TimeoutSolver {
    let timeout_solver = move |expr, timeout| {
        let recv = CancelToken::new();
        let send = recv.clone();
        std::thread::spawn(move || {
            std::thread::sleep(timeout);
            send.cancel();
        });
        cancelable(expr, recv)
    };
    Box::new(timeout_solver)
}
