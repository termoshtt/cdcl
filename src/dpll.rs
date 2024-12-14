use crate::{take_minimal_id, Literal, Solution, State, CNF};

#[async_recursion::async_recursion]
pub async fn dpll(mut input: CNF) -> Solution {
    let mut state = State::default();

    // Unit propagation
    loop {
        let units = input.take_unit_clauses();
        if units.is_empty() {
            break;
        }
        for lit in units.into_iter() {
            if input.substitute(lit).is_err() {
                return Solution::UnSat;
            }
            state.insert(lit);
        }
    }

    match input.is_solved() {
        Some(Solution::Sat(..)) => return Solution::Sat(state),
        Some(Solution::UnSat) => return Solution::UnSat,
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
        if new.substitute(lit).is_err() {
            continue;
        }
        match dpll(new).await {
            Solution::Sat(mut sub_state) => {
                state.append(&mut sub_state);
                state.insert(lit);
                return Solution::Sat(state);
            }
            Solution::UnSat => continue,
        }
    }
    Solution::UnSat
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block_on;

    #[test]
    fn test_dpll() {
        for (expr, expected) in crate::testing::single_solution_cases() {
            assert_eq!(block_on(dpll(expr.clone())), expected, "Failed on {expr:?}",);
        }
    }
}
