use crate::{CancelToken, Expr, Solution, State, CNF};

pub fn dpll(mut input: CNF, selector: fn(&CNF) -> usize, cancel_token: CancelToken) -> Solution {
    match *input.as_expr() {
        // Already solved
        Expr::True => return Solution::Sat(State::default()),
        // Never feasible
        Expr::False => return Solution::UnSat,
        _ => {}
    }

    if cancel_token.is_canceled() {
        log::info!("Canceled");
        return Solution::Canceled;
    }

    // Unit propagation
    loop {
        let (state, mut removed) = input.take_unit_clauses();
        if state.is_empty() {
            assert_eq!(removed, input);
            break;
        }
        for (id, value) in state.into_iter() {
            removed = removed.substitute(id, value);
        }
        input = removed;
    }

    let fix = selector(&input);
    for value in [true, false] {
        log::trace!("Set x{} = {}", fix, value);
        match dpll(input.substitute(fix, value), selector, cancel_token.clone()) {
            Solution::Sat(mut state) => {
                state.insert(fix, value);
                return Solution::Sat(state);
            }
            Solution::UnSat => continue,
            Solution::Canceled => return Solution::Canceled,
        }
    }
    Solution::UnSat
}
