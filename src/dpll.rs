use crate::{CancelToken, Expr, Solution, State, CNF};

pub fn dpll(mut input: CNF, selector: fn(&CNF) -> usize, cancel_token: CancelToken) -> Solution {
    let mut state = State::default();

    // Unit propagation
    loop {
        if cancel_token.is_canceled() {
            return Solution::Canceled;
        }
        let (units, mut removed) = input.take_unit_clauses();
        if units.is_empty() {
            assert_eq!(removed, input);
            break;
        }
        for (id, value) in units.into_iter() {
            removed = removed.substitute(id, value);
            state.insert(id, value);
        }
        input = removed;
    }

    match *input.as_expr() {
        // Already solved
        Expr::True => return Solution::Sat(state),
        // Never feasible
        Expr::False => return Solution::UnSat,
        _ => {}
    }

    let fix = selector(&input);
    for value in [true, false] {
        log::trace!("Set x{} = {}", fix, value);
        match dpll(input.substitute(fix, value), selector, cancel_token.clone()) {
            Solution::Sat(mut sub_state) => {
                state.append(&mut sub_state);
                state.insert(fix, value);
                return Solution::Sat(state);
            }
            Solution::UnSat => continue,
            Solution::Canceled => return Solution::Canceled,
        }
    }
    Solution::UnSat
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dpll() {
        let cancel_token = CancelToken::new();

        for (expr, expected) in crate::testing::single_solution_cases() {
            assert_eq!(
                dpll(expr.clone(), crate::take_minimal_id, cancel_token.clone()),
                expected,
                "Failed on {expr:?}",
            );
        }
    }
}
