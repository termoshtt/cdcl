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
/// Logical variables represented by [Expr::Var] have unique integer IDs. They are displayed as `x` followed by the ID.
///
/// ```rust
/// use cdcl::Expr;
///
/// // Create a expression consists of a variable with id 0
/// let expr = Expr::variable(0);
/// assert_eq!(expr.to_string(), "x0");
/// ```
///
/// [Expr::True] and [Expr::False] constants
///
/// ```rust
/// use cdcl::Expr;
///
/// let t = Expr::True;
/// let f = Expr::False;
///
/// // Displayed as 1 and 0
/// assert_eq!(t.to_string(), "1");
/// assert_eq!(f.to_string(), "0");
///
/// // From bool
/// assert_eq!(Expr::from(true), t);
/// assert_eq!(Expr::from(false), f);
/// ```
///
/// [BitAnd] (`&`), [BitOr] (`|`), and [Not] (`!`) operators can be used to construct ∧, ∨, and ¬ operations.
/// Note that the precedence of `&` is higher than `|`.
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
/// Different from [CNF] and [DNF], these expressions are kept as created except for following cases:
///
/// ```rust
/// use cdcl::Expr;
///
/// // ¬¬x0 = x0
/// assert_eq!(!!Expr::variable(0), Expr::variable(0));
///
/// // x0 ∧ x0 = x0
/// assert_eq!(Expr::variable(0) & Expr::variable(0), Expr::variable(0));
/// // x0 ∨ x0 = x0
/// assert_eq!(Expr::variable(0) | Expr::variable(0), Expr::variable(0));
///
/// // x0 ∨ ¬x0 = 1
/// assert_eq!(Expr::variable(0) | !Expr::variable(0), Expr::True);
/// assert_eq!(!Expr::variable(0) | Expr::variable(0), Expr::True);
/// // x0 ∧ ¬x0 = 0
/// assert_eq!(Expr::variable(0) & !Expr::variable(0), Expr::False);
/// assert_eq!(!Expr::variable(0) & Expr::variable(0), Expr::False);
///
/// // ¬1 = 0
/// assert_eq!(!Expr::True, Expr::False);
/// // ¬0 = 1
/// assert_eq!(!Expr::False, Expr::True);
///
/// // 1 ∧ x0 = x0
/// assert_eq!(Expr::True & Expr::variable(0), Expr::variable(0));
/// assert_eq!(Expr::variable(0) & Expr::True, Expr::variable(0));
/// // 0 ∨ x0 = x0
/// assert_eq!(Expr::False | Expr::variable(0), Expr::variable(0));
/// assert_eq!(Expr::variable(0) | Expr::False, Expr::variable(0));
/// // 1 ∨ x0 = 1
/// assert_eq!(Expr::True | Expr::variable(0), Expr::True);
/// assert_eq!(Expr::variable(0) | Expr::True, Expr::True);
/// // 0 ∧ x0 = 0
/// assert_eq!(Expr::False & Expr::variable(0), Expr::False);
/// assert_eq!(Expr::variable(0) & Expr::False, Expr::False);
/// ```
///
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    Not(Box<Expr>),

    /// Propositional variable.
    Var {
        /// Unique identifier for the variable.
        id: usize,
    },
    /// True constant, displayed as `1`.
    True,
    /// False constant, displayed as `0`.
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
        // Double negation elimination
        match self {
            Expr::Not(e) => *e,
            Expr::True => Expr::False,
            Expr::False => Expr::True,
            _ => Expr::Not(Box::new(self)),
        }
    }
}

impl fmt::Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
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
            Expr::True => write!(f, "1"),
            Expr::False => write!(f, "0"),
        }
    }
}
