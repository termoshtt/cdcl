use maplit::btreeset;
use std::{
    collections::BTreeSet,
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
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    /// Conjunction of expressions. Since `AND` is commutative, the expressions are sorted.
    And(BTreeSet<Expr>),
    Or(BTreeSet<Expr>),
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

    /// Height of the expression.
    ///
    /// ```rust
    /// use cdcl::Expr;
    ///
    /// // Height of a variable and a literal is `1`
    /// assert_eq!(Expr::True.height(), 1);
    /// assert_eq!(Expr::variable(0).height(), 1);
    ///
    /// // Height of a NOT expression is `2`
    /// assert_eq!((!Expr::variable(0)).height(), 2);
    ///
    /// // Since the AND and OR expressions are flatten, their height is the maximum height of the children plus 1
    /// assert_eq!((Expr::variable(0) & Expr::variable(1)).height(), 2);
    /// assert_eq!((Expr::variable(0) & Expr::variable(1) & Expr::variable(2)).height(), 2);
    /// assert_eq!((Expr::variable(0) | Expr::variable(1)).height(), 2);
    /// assert_eq!((Expr::variable(0) | Expr::variable(1) | Expr::variable(2)).height(), 2);
    ///
    /// // Height of a nested expression
    /// assert_eq!((Expr::variable(0) & (Expr::variable(1) | Expr::variable(2))).height(), 3);
    /// assert_eq!((Expr::variable(0) & (Expr::variable(1) | !Expr::variable(2))).height(), 4);
    /// ```
    ///
    pub fn height(&self) -> usize {
        match self {
            Expr::And(inner) | Expr::Or(inner) => {
                inner.iter().map(|e| e.height()).max().unwrap_or(0) + 1
            }
            Expr::Not(e) => e.height() + 1,
            _ => 1,
        }
    }

    pub fn substitute(&self, id: usize, value: bool) -> Expr {
        match self {
            Expr::Var { id: var_id } if *var_id == id => value.into(),
            Expr::Var { .. } => self.clone(),
            Expr::Not(e) => !e.substitute(id, value),
            Expr::And(inner) => inner
                .iter()
                .map(|e| e.substitute(id, value))
                .fold(Expr::True, |acc, e| acc & e),
            Expr::Or(inner) => inner
                .iter()
                .map(|e| e.substitute(id, value))
                .fold(Expr::False, |acc, e| acc | e),
            _ => self.clone(),
        }
    }

    /// IDs of using variables in the expression.
    pub fn variables(&self) -> BTreeSet<usize> {
        match self {
            Expr::Var { id } => btreeset![*id],
            Expr::Not(e) => e.variables(),
            Expr::And(inner) | Expr::Or(inner) => {
                inner.iter().flat_map(|e| e.variables()).collect()
            }
            _ => Default::default(),
        }
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
        Some(self.cmp(other))
    }
}

impl Ord for Expr {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering;
        match (self, other) {
            // Bool literals are smaller than others, and False is smallest
            (Expr::False, Expr::False) | (Expr::True, Expr::True) => Ordering::Equal,
            (Expr::False, _) => Ordering::Less,
            (_, Expr::False) => Ordering::Greater,
            (Expr::True, _) => Ordering::Less,
            (_, Expr::True) => Ordering::Greater,

            // NOT of any expression is next to the expression
            (Expr::Not(a), Expr::Not(b)) => a.cmp(b),
            (Expr::Not(a), b) if a.as_ref() == b => Ordering::Greater,
            (Expr::Not(a), b) => a.as_ref().cmp(b),
            (a, Expr::Not(b)) if a == b.as_ref() => Ordering::Less,
            (a, Expr::Not(b)) => a.cmp(b),

            (Expr::Var { id: a }, Expr::Var { id: b }) => a.cmp(b),
            (Expr::Var { .. }, _) => Ordering::Less,
            (_, Expr::Var { .. }) => Ordering::Greater,

            (Expr::And(lhs), Expr::And(rhs)) if lhs.len() != rhs.len() => lhs.len().cmp(&rhs.len()),
            (Expr::And(lhs), Expr::And(rhs)) => lhs.cmp(rhs),
            (Expr::And(_), _) => Ordering::Less,
            (_, Expr::And(_)) => Ordering::Greater,

            (Expr::Or(lhs), Expr::Or(rhs)) if lhs.len() != rhs.len() => lhs.len().cmp(&rhs.len()),
            (Expr::Or(lhs), Expr::Or(rhs)) => lhs.cmp(rhs),
        }
    }
}

fn has_prop_and_its_neg(exprs: &BTreeSet<Expr>) -> bool {
    if exprs.len() < 2 {
        return false;
    }
    let mut iter = exprs.iter();
    // NOT of any expression is next to the expression
    let mut last = iter.next().unwrap();
    for current in iter {
        match current {
            Expr::Not(c) if c.as_ref() == last => return true,
            _ => {}
        }
        last = current;
    }
    false
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
                if has_prop_and_its_neg(&lhs) {
                    return Expr::False;
                }
                Expr::And(lhs)
            }
            (Expr::And(mut a), b) | (b, Expr::And(mut a)) => {
                a.insert(b);
                if has_prop_and_its_neg(&a) {
                    return Expr::False;
                }
                Expr::And(a)
            }
            (lhs, rhs) => Expr::And(btreeset! {lhs, rhs}),
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
                if has_prop_and_its_neg(&lhs) {
                    return Expr::True;
                }
                Expr::Or(lhs)
            }
            (Expr::Or(mut a), b) | (b, Expr::Or(mut a)) => {
                a.insert(b);
                if has_prop_and_its_neg(&a) {
                    return Expr::True;
                }
                Expr::Or(a)
            }
            (lhs, rhs) => Expr::Or(btreeset! { lhs, rhs }),
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dedup() {
        // x0 ∧ x1 ∧ x0 = x0 ∧ x1
        assert_eq!(
            Expr::variable(0) & Expr::variable(1) & Expr::variable(0),
            Expr::variable(0) & Expr::variable(1),
        );

        // x0 ∨ x1 ∨ x0 = x0 ∨ x1
        assert_eq!(
            Expr::variable(0) | Expr::variable(1) | Expr::variable(0),
            Expr::variable(0) | Expr::variable(1),
        );
    }

    #[test]
    fn contradiction() {
        // x0 ∧ x1 ∧ ¬x0 = 0
        assert_eq!(
            Expr::variable(0) & Expr::variable(1) & !Expr::variable(0),
            Expr::False
        );

        // x0 ∨ x1 ∨ ¬x0 = 1
        assert_eq!(
            Expr::variable(0) & Expr::variable(1) & !Expr::variable(0),
            Expr::False
        );
    }
}
