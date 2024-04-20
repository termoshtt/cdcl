use super::Expr;

/// Expression in Conjunctive Normal Form
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CNF(Expr);
