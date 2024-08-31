use crate::{expr::CNF, Clause};

#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct DecisionLevel {
    decision: usize,
    implicated: Vec<(usize, CNF)>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CDCL {
    expr: CNF,
    selector: fn(&CNF) -> usize,
    trail: Vec<DecisionLevel>,
}

enum ClauseState {
    /// Clause is satisfied for given the Trail state
    Satisfied,
    /// Clause is conflicting
    Conflict,
    /// Clause contains a single unassigned literal
    Unit(usize, bool),
    /// Clause contains two or more unassigned literals
    Undetermined,
}

pub fn check_clause(trail: &[DecisionLevel], clause: &Clause) -> ClauseState {
    todo!()
}

impl CDCL {
    pub fn new(expr: CNF, selector: fn(&CNF) -> usize) -> Self {
        Self {
            expr,
            selector,
            trail: vec![],
        }
    }
}
