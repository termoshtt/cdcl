use crate::{Expr, State, CNF};

pub fn brute_force(input: CNF) -> Option<State> {
    match input.as_expr() {
        // Already solved
        &Expr::True => return Some(State::default()),
        // Never feasible
        &Expr::False => return None,
        _ => {}
    }

    let variables = input.variables();
    let fix = variables
        .first()
        .expect("Non-boolean CNF expression must have at least one variable.");

    for value in [true, false] {
        if let Some(mut state) = brute_force(input.substitute(*fix, value)) {
            state.insert(*fix, value);
            return Some(state);
        }
    }

    None
}
