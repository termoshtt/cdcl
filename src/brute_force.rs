use crate::{Expr, State, CNF};

pub fn brute_force(input: CNF) -> Option<State> {
    let mut state = State::default();
    let mut stack: Vec<usize> = Vec::new();
    loop {
        for clause in input.clauses() {
            match clause.partial_eval(&state) {
                Expr::True => continue,
                Expr::False => {
                    // Backtrack
                    todo!()
                }
                expr @ _ => todo!(),
            }
        }
    }
    todo!()
}
