use super::{Expr, State};
use anyhow::Result;
use std::{
    collections::BTreeSet,
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

impl std::ops::Deref for CNF {
    type Target = Expr;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<bool> for CNF {
    fn from(value: bool) -> Self {
        CNF(Expr::from(value))
    }
}

impl CNF {
    pub fn from_rgbd(cnf: rgbd::CNF) -> Self {
        let inner = cnf
            .clauses
            .into_iter()
            .map(|clause| {
                let inner = clause
                    .into_iter()
                    .map(|var| {
                        if var >= 0 {
                            Expr::variable(var as usize)
                        } else {
                            !Expr::variable((-var) as usize)
                        }
                    })
                    .collect::<BTreeSet<Expr>>();
                Expr::Or(inner)
            })
            .collect();
        Self(Expr::And(inner))
    }

    /// Parse CNF from DIMACS format
    ///
    /// ```rust
    /// use cdcl::CNF;
    ///
    /// let expr = CNF::from_dimacs_format(r#"
    /// p cnf 5 3
    /// 1 -5 4 0
    /// -1 5 3 4 0
    /// -3 -4 0
    /// "#).unwrap();
    ///
    /// // Note the expression are sorted automatically
    /// assert_eq!(
    ///     expr.to_string(),
    ///     "(¬x3 ∨ ¬x4) ∧ (x1 ∨ x4 ∨ ¬x5) ∧ (¬x1 ∨ x3 ∨ x4 ∨ x5)"
    /// );
    /// ```
    pub fn from_dimacs_format(input: &str) -> Result<Self> {
        let cnf = rgbd::CNF::from_dimacs_format_str(input)?;
        Ok(Self::from_rgbd(cnf))
    }

    pub fn variable(id: usize) -> Self {
        CNF(Expr::Var { id })
    }

    pub fn as_expr(&self) -> &Expr {
        &self.0
    }

    pub fn substitute(&self, id: usize, value: bool) -> Self {
        CNF(self.0.substitute(id, value))
    }

    /// Clauses in AND expression
    ///
    /// ```rust
    /// use cdcl::{CNF, Expr};
    ///
    /// // (x0 ∧ x1) ∨ x2 = (x0 ∨ x2) ∧ (x1 ∨ x2)
    /// let expr = (CNF::variable(0) & CNF::variable(1)) | CNF::variable(2);
    /// let clauses = expr.clauses().cloned().collect::<Vec<Expr>>();
    /// assert_eq!(
    ///     clauses,
    ///     vec![
    ///         Expr::variable(0) | Expr::variable(2), // x0 ∨ x2
    ///         Expr::variable(1) | Expr::variable(2)  // x1 ∨ x2
    ///     ]
    /// );
    ///
    /// // Non-AND expression is a single clause
    /// let expr = CNF::variable(0);
    /// let clauses = expr.clauses().cloned().collect::<Vec<Expr>>();
    /// assert_eq!(clauses, vec![Expr::variable(0)]);
    ///
    /// let expr = CNF::variable(0) | CNF::variable(1);
    /// let clauses = expr.clauses().cloned().collect::<Vec<Expr>>();
    /// assert_eq!(clauses, vec![Expr::variable(0) | Expr::variable(1)]);
    /// ```
    ///
    pub fn clauses(&self) -> Box<dyn Iterator<Item = &Expr> + '_> {
        match &self.0 {
            Expr::And(inner) => Box::new(inner.iter()),
            expr => Box::new(Some(expr).into_iter()),
        }
    }

    /// List up all unit clauses, single variable or its negation, as a [State] with remaining clauses as a new [CNF]
    ///
    /// ```rust
    /// use cdcl::{CNF, State, Expr};
    /// use maplit::btreemap;
    ///
    /// // x0 ∧ x1
    /// let expr = CNF::variable(0) & CNF::variable(1);
    /// let (state, cnf) = expr.take_unit_clauses();
    /// assert_eq!(state, btreemap! { 0 => true, 1 => true });
    /// assert_eq!(cnf, CNF::from(true));
    ///
    /// // x0 ∧ x1 ∧ (x2 ∨ x3)
    /// let expr = CNF::variable(0) & CNF::variable(1) & (CNF::variable(2) | CNF::variable(3));
    /// let (state, cnf) = expr.take_unit_clauses();
    /// assert_eq!(state, btreemap! { 0 => true, 1 => true });
    /// assert_eq!(cnf, CNF::variable(2) | CNF::variable(3));
    /// ```
    pub fn take_unit_clauses(&self) -> (State, CNF) {
        let mut state = State::new();
        let mut clauses = BTreeSet::new();
        for clause in self.clauses() {
            match clause {
                Expr::Var { id } => {
                    state.insert(*id, true);
                }
                Expr::Not(expr) => {
                    if let Expr::Var { id } = expr.as_ref() {
                        state.insert(*id, false);
                    } else {
                        clauses.insert(clause.clone());
                    }
                }
                clause => {
                    clauses.insert(clause.clone());
                }
            }
        }
        (
            state,
            CNF(match clauses.len() {
                0 => Expr::True,
                1 => clauses.first().unwrap().clone(),
                _ => Expr::And(clauses),
            }),
        )
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
                let mut result = BTreeSet::new();
                for a in &lhs {
                    for b in &rhs {
                        result.insert(a.clone() | b.clone());
                    }
                }
                CNF(Expr::And(result))
            }
            (Expr::And(inner), c) | (c, Expr::And(inner)) => {
                // (a ∧ b) ∨ c = (a ∨ c) ∧ (b ∨ c)
                CNF(Expr::And(
                    inner.into_iter().map(|a| a | c.clone()).collect(),
                ))
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
            Expr::And(inner) => CNF(Expr::Or(inner.into_iter().map(Not::not).collect())),
            Expr::Or(inner) => CNF(Expr::And(inner.into_iter().map(Not::not).collect())),
            a => CNF(!a),
        }
    }
}
