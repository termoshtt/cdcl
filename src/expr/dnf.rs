use super::Expr;
use std::fmt;

/// Expression in Disjunctive Normal Form
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct DNF(Expr);

impl fmt::Debug for DNF {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Display for DNF {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
