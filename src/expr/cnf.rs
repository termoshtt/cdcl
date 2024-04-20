use super::Expr;
use std::fmt;

/// Expression in Conjunctive Normal Form
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct CNF(Expr);

impl fmt::Debug for CNF {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Display for CNF {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
