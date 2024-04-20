use super::Expr;
use std::{
    fmt,
    ops::{BitAnd, BitOr, Not},
};

/// Expression in Conjunctive Normal Form
///
/// # Examples
///
/// ```rust
/// use cdcl::CNF;
///
/// // (x0 ∧ x1) ∨ x2 is not in CNF form, and normalized into (x0 ∧ x2) ∨ (x1 ∧ x2).
/// let expr = (CNF::variable(0) & CNF::variable(1)) | CNF::variable(2);
/// assert_eq!(expr.to_string(), "(x0 ∧ x2) ∨ (x1 ∧ x2)");
/// ```
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct CNF(Expr);

impl CNF {
    pub fn variable(id: usize) -> Self {
        CNF(Expr::Var { id })
    }
}

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

impl BitAnd for CNF {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self {
        CNF(self.0 & rhs.0)
    }
}

impl BitOr for CNF {
    type Output = Self;

    fn bitor(self, _rhs: Self) -> Self {
        // Distributive Law
        todo!()
    }
}

impl Not for CNF {
    type Output = Self;

    fn not(self) -> Self {
        // De Morgan's Law
        todo!()
    }
}
