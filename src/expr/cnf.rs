use super::Expr;
use std::{
    fmt,
    ops::{BitAnd, BitOr, Not},
};

/// An [Expr] in [Conjunctive Normal Form](https://en.wikipedia.org/wiki/Conjunctive_normal_form)
///
/// ```rust
/// use cdcl::CNF;
///
/// // (x0 ∧ x1) ∨ x2 = (x0 ∨ x2) ∧ (x1 ∨ x2)
/// let expr = (CNF::variable(0) & CNF::variable(1)) | CNF::variable(2);
/// assert_eq!(expr.to_string(), "(x0 ∨ x2) ∧ (x1 ∨ x2)");
///
/// // x0 ∨ (x1 ∧ x2) = (x0 ∨ x1) ∧ (x0 ∨ x2)
/// let expr = CNF::variable(0) | (CNF::variable(1) & CNF::variable(2));
/// assert_eq!(expr.to_string(), "(x0 ∨ x1) ∧ (x0 ∨ x2)");
///
/// // (x0 ∧ x1) ∨ (x2 ∧ x3) = (x0 ∨ x2) ∧ (x0 ∨ x3) ∧ (x1 ∨ x2) ∧ (x1 ∨ x3)
/// let expr = (CNF::variable(0) & CNF::variable(1)) | (CNF::variable(2) & CNF::variable(3));
/// assert_eq!(expr.to_string(), "(x0 ∨ x2) ∧ (x0 ∨ x3) ∧ (x1 ∨ x2) ∧ (x1 ∨ x3)");
///
/// // ¬(x0 ∧ x1) = ¬x0 ∨ ¬x1
/// let expr = !(CNF::variable(0) & CNF::variable(1));
/// assert_eq!(expr.to_string(), "¬x0 ∨ ¬x1");
///
/// // ¬(x0 ∨ x1) ∧ x2 = ¬x0 ∧ ¬x1 ∧ x2
/// let expr = !(CNF::variable(0) | CNF::variable(1)) & CNF::variable(2);
/// assert_eq!(expr.to_string(), "¬x0 ∧ ¬x1 ∧ x2");
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

    fn bitor(self, rhs: Self) -> Self {
        // Distributive Law
        match (self.0, rhs.0) {
            (Expr::And(lhs), Expr::And(rhs)) => {
                // (a ∧ b) ∨ (c ∧ d) = (a ∨ c) ∧ (a ∨ d) ∧ (b ∨ c) ∧ (b ∨ d)
                todo!()
            }
            (Expr::And(lhs), c) => {
                // (a ∧ b) ∨ c = (a ∨ c) ∧ (b ∨ c)
                todo!()
            }
            (a, Expr::And(rhs)) => {
                // a ∨ (c ∧ d) = (a ∨ c) ∧ (a ∨ d)
                todo!()
            }
            (lhs, rhs) => CNF(lhs | rhs),
        }
    }
}

impl Not for CNF {
    type Output = Self;

    fn not(self) -> Self {
        // De Morgan's Law
        match self.0 {
            Expr::And(inner) => todo!(),
            Expr::Or(a, b) => CNF(!*a & !*b),
            a => CNF(!a),
        }
    }
}
