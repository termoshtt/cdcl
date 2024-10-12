use crate::{take_minimal_id, CancelToken, Cancelable, Literal, Solution, State, CNF};

pub fn dpll(mut input: CNF, cancel_token: CancelToken) -> Cancelable<Solution> {
    let mut state = State::default();

    // Unit propagation
    loop {
        cancel_token.is_canceled()?;
        let units = input.take_unit_clauses();
        if units.is_empty() {
            break;
        }
        for lit in units.into_iter() {
            input.substitute(lit);
            state.insert(lit);
        }
    }

    match input.is_solved() {
        Some(Solution::Sat(..)) => return Ok(Solution::Sat(state)),
        Some(Solution::UnSat) => return Ok(Solution::UnSat),
        _ => {}
    }

    let fix = take_minimal_id(&input);
    for value in [true, false] {
        let lit = Literal {
            id: fix,
            positive: value,
        };
        log::trace!("Decision: {}", lit);
        let mut new = input.clone();
        new.substitute(lit);
        match dpll(new, cancel_token.clone())? {
            Solution::Sat(mut sub_state) => {
                state.append(&mut sub_state);
                state.insert(lit);
                return Ok(Solution::Sat(state));
            }
            Solution::UnSat => continue,
        }
    }
    Ok(Solution::UnSat)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dpll() {
        for (expr, expected) in crate::testing::single_solution_cases() {
            assert_eq!(
                dpll(expr.clone(), CancelToken::new()).unwrap(),
                expected,
                "Failed on {expr:?}",
            );
        }
    }
}
