use std::{
    fmt,
    ops::{BitAnd, BitOr, Not},
};

mod cnf;
mod dnf;

pub use cnf::CNF;
pub use dnf::DNF;

/// Expression in propositional (or Boolean) logic.
///
/// This does not assume that the expression is in conjunctive (CNF) or disjunctive normal form (DNF).
///
/// # Examples
///
/// [BitAnd] (`&`), [BitOr] (`|`), and [Not] (`!`) operators can be used to construct ∧, ∨, and ¬ operations.
///
/// ```rust
/// use cdcl::Expr;
///
/// let expr = Expr::variable(0) & Expr::variable(1) | Expr::variable(2);
/// assert_eq!(expr.to_string(), "(x0 ∧ x1) ∨ x2");
///
/// let expr = Expr::variable(0) | Expr::variable(1) & Expr::variable(2);
/// assert_eq!(expr.to_string(), "x0 ∨ (x1 ∧ x2)");
///
/// let expr = !Expr::variable(0) & Expr::variable(1);
/// assert_eq!(expr.to_string(), "¬x0 ∧ x1");
/// ```
///
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    Not(Box<Expr>),

    /// Propositional variable.
    Var {
        /// Unique identifier for the variable.
        id: usize,
    },
    /// True constant.
    True,
    /// False constant.
    False,
}

impl Expr {
    /// Propositional variable.
    pub fn variable(id: usize) -> Expr {
        Expr::Var { id }
    }

    /// Returns the conjunctive normal form of the expression.
    pub fn cnf(self) -> Expr {
        todo!()
    }
}

impl From<usize> for Expr {
    fn from(id: usize) -> Self {
        Expr::variable(id)
    }
}

impl From<bool> for Expr {
    fn from(b: bool) -> Self {
        if b {
            Expr::True
        } else {
            Expr::False
        }
    }
}

impl BitAnd for Expr {
    type Output = Expr;
    fn bitand(self, rhs: Self) -> Self::Output {
        Expr::And(Box::new(self), Box::new(rhs))
    }
}

impl BitOr for Expr {
    type Output = Expr;
    fn bitor(self, rhs: Self) -> Self::Output {
        Expr::Or(Box::new(self), Box::new(rhs))
    }
}

impl Not for Expr {
    type Output = Expr;
    fn not(self) -> Self::Output {
        Expr::Not(Box::new(self))
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expr::And(lhs, rhs) => {
                match lhs.as_ref() {
                    Expr::Or(_, _) => write!(f, "({})", lhs)?,
                    _ => write!(f, "{}", lhs)?,
                }
                write!(f, " ∧ ")?;
                match rhs.as_ref() {
                    Expr::Or(_, _) => write!(f, "({})", rhs),
                    _ => write!(f, "{}", rhs),
                }
            }
            Expr::Or(lhs, rhs) => {
                match lhs.as_ref() {
                    Expr::And(_, _) => write!(f, "({})", lhs)?,
                    _ => write!(f, "{}", lhs)?,
                }
                write!(f, " ∨ ")?;
                match rhs.as_ref() {
                    Expr::And(_, _) => write!(f, "({})", rhs),
                    _ => write!(f, "{}", rhs),
                }
            }
            Expr::Not(e) => write!(f, "¬{}", e),
            Expr::Var { id } => write!(f, "x{}", id),
            Expr::True => write!(f, "⊤"),
            Expr::False => write!(f, "⊥"),
        }
    }
}
