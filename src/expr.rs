use std::{
    fmt,
    ops::{BitAnd, BitOr, Not},
};

mod cnf;
mod dnf;

pub use cnf::CNF;
pub use dnf::DNF;

/// Expression in Boolean logic.
///
/// This does not assume that the expression is in conjunctive ([CNF]) or disjunctive normal form ([DNF]).
///
/// Logical variables is represented by [Expr::Var], and have unique integer IDs.
/// They are displayed as `x` followed by the ID like `x0`.
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
/// assert_eq!(expr.to_string(), "x2 ∨ (x0 ∧ x1)");
///
/// let expr = Expr::variable(0) | Expr::variable(1) & Expr::variable(2);
/// assert_eq!(expr.to_string(), "x0 ∨ (x1 ∧ x2)");
///
/// let expr = !Expr::variable(0) & Expr::variable(1);
/// assert_eq!(expr.to_string(), "¬x0 ∧ x1");
///
/// // AND and OR expressions are automatically sorted
/// let expr = Expr::variable(2) & Expr::variable(0) & !Expr::variable(1);
/// assert_eq!(expr.to_string(), "x0 ∧ ¬x1 ∧ x2");
/// let expr = Expr::variable(2) | Expr::variable(0) | !Expr::variable(1);
/// assert_eq!(expr.to_string(), "x0 ∨ ¬x1 ∨ x2");
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
/// The expressions have ordering as following:
///
/// ```rust
/// use cdcl::Expr;
///
/// // Bool literals are smaller than others, and False is smallest
/// assert!(Expr::False < Expr::True);
/// assert!(Expr::True < Expr::variable(0));
/// assert!(Expr::True < Expr::variable(0) & Expr::variable(1));
/// assert!(Expr::True < Expr::variable(0) | Expr::variable(1));
/// assert!(Expr::True < !Expr::variable(0));
///
/// // Smaller variable ID is smaller
/// assert!(Expr::variable(0) < Expr::variable(1));
///
/// // NOT of any expression is next to the expression
/// assert!(Expr::variable(0) < !Expr::variable(0));
/// assert!(!Expr::variable(0) < Expr::variable(1));
///
/// // AND is smaller than OR
/// assert!(Expr::variable(0) & Expr::variable(1) < Expr::variable(0) | Expr::variable(1));
///
/// // AND and OR expressions have graded lexical ordering
/// // lexical order for same rank AND
/// assert!(Expr::variable(0) & Expr::variable(1) < Expr::variable(0) & Expr::variable(2));
/// // rank-2 AND is smaller than rank-3 AND
/// assert!(Expr::variable(1) & Expr::variable(2) < Expr::variable(0) & Expr::variable(1) & Expr::variable(2));
/// ```
///
#[derive(Clone, PartialEq, Eq, Ord, Hash)]
pub enum Expr {
    /// Conjunction of expressions. Since `AND` is commutative, the expressions are sorted.
    And(Vec<Expr>),
    Or(Vec<Expr>),
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

impl PartialOrd for Expr {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        use std::cmp::Ordering;
        match (self, other) {
            // Bool literals are smaller than others, and False is smallest
            (Expr::False, Expr::False) | (Expr::True, Expr::True) => Some(Ordering::Equal),
            (Expr::False, _) => Some(Ordering::Less),
            (_, Expr::False) => Some(Ordering::Greater),
            (Expr::True, _) => Some(Ordering::Less),
            (_, Expr::True) => Some(Ordering::Greater),

            // NOT of any expression is next to the expression
            (Expr::Not(a), Expr::Not(b)) => a.partial_cmp(b),
            (Expr::Not(a), b) if a.as_ref() == b => Some(Ordering::Greater),
            (Expr::Not(a), b) => a.as_ref().partial_cmp(b),
            (a, Expr::Not(b)) if a == b.as_ref() => Some(Ordering::Less),
            (a, Expr::Not(b)) => a.partial_cmp(b),

            (Expr::Var { id: a }, Expr::Var { id: b }) => a.partial_cmp(b),
            (Expr::Var { .. }, _) => Some(Ordering::Less),
            (_, Expr::Var { .. }) => Some(Ordering::Greater),

            (Expr::And(lhs), Expr::And(rhs)) if lhs.len() != rhs.len() => {
                lhs.len().partial_cmp(&rhs.len())
            }
            (Expr::And(lhs), Expr::And(rhs)) => lhs.partial_cmp(rhs),
            (Expr::And(_), _) => Some(Ordering::Less),
            (_, Expr::And(_)) => Some(Ordering::Greater),

            (Expr::Or(lhs), Expr::Or(rhs)) if lhs.len() != rhs.len() => {
                lhs.len().partial_cmp(&rhs.len())
            }
            (Expr::Or(lhs), Expr::Or(rhs)) => lhs.partial_cmp(rhs),
        }
    }
}

impl BitAnd for Expr {
    type Output = Expr;
    fn bitand(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Expr::False, _) | (_, Expr::False) => Expr::False,
            (Expr::True, x) | (x, Expr::True) => x,
            (x, Expr::Not(y)) | (Expr::Not(y), x) if x == *y => Expr::False,
            (lhs, rhs) if lhs == rhs => lhs,
            (Expr::And(mut lhs), Expr::And(mut rhs)) => {
                lhs.append(&mut rhs);
                lhs.sort_unstable();
                Expr::And(lhs)
            }
            (Expr::And(mut a), b) | (b, Expr::And(mut a)) => {
                a.push(b);
                a.sort_unstable();
                Expr::And(a)
            }
            (lhs, rhs) => Expr::And(if lhs < rhs {
                vec![lhs, rhs]
            } else {
                vec![rhs, lhs]
            }),
        }
    }
}

impl BitOr for Expr {
    type Output = Expr;
    fn bitor(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Expr::True, _) | (_, Expr::True) => Expr::True,
            (Expr::False, x) | (x, Expr::False) => x,
            (x, Expr::Not(y)) | (Expr::Not(y), x) if x == *y => Expr::True,
            (lhs, rhs) if lhs == rhs => lhs,
            (Expr::Or(mut lhs), Expr::Or(mut rhs)) => {
                lhs.append(&mut rhs);
                lhs.sort_unstable();
                Expr::Or(lhs)
            }
            (Expr::Or(mut a), b) | (b, Expr::Or(mut a)) => {
                a.push(b);
                a.sort_unstable();
                Expr::Or(a)
            }
            (lhs, rhs) => Expr::Or(if lhs < rhs {
                vec![lhs, rhs]
            } else {
                vec![rhs, lhs]
            }),
        }
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
            Expr::And(inner) => {
                for (i, e) in inner.iter().enumerate() {
                    if i != 0 {
                        write!(f, " ∧ ")?;
                    }
                    match e {
                        Expr::Or(_) => write!(f, "({})", e)?,
                        _ => write!(f, "{}", e)?,
                    }
                }
                Ok(())
            }
            Expr::Or(inner) => {
                for (i, e) in inner.iter().enumerate() {
                    if i != 0 {
                        write!(f, " ∨ ")?;
                    }
                    match e {
                        Expr::And(_) => write!(f, "({})", e)?,
                        _ => write!(f, "{}", e)?,
                    }
                }
                Ok(())
            }
            Expr::Not(e) => write!(f, "¬{}", e),
            Expr::Var { id } => write!(f, "x{}", id),
            Expr::True => write!(f, "1"),
            Expr::False => write!(f, "0"),
        }
    }
}
