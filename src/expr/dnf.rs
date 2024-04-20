use super::Expr;

/// Expression in Disjunctive Normal Form
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DNF(Expr);
