/// Expression in propositional logic.
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    Not(Box<Expr>),

    // Literals
    /// Propositional variable.
    Var(String),
    /// True constant.
    True,
    /// False constant.
    False,
}

impl Expr {
    /// Propositional variable.
    pub fn variable(name: String) -> Expr {
        Expr::Var(name)
    }

    /// Returns the conjunctive normal form of the expression.
    pub fn cnf(self) -> Expr {
        todo!()
    }
}
