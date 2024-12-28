use crate::{pending_once, take_minimal_id, Literal, Solution, State, CNF};

#[async_recursion::async_recursion]
pub async fn dpll(mut input: CNF) -> Solution {
    let mut state = State::default();

    // Unit propagation
    loop {
        pending_once().await;
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
            _ => continue,
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

    #[test]
    fn test_dpll_solve_sat() {
        const DATASET: [&str; 3] = [
            "7e19f295d35c30ac4d5386ffec1fcf28",
            "866f6730afd797a244fea4f28ac3a218",
            "8345bdb88fa777b2940145d3306bbf7e",
        ];
        for digest in DATASET {
            let expr = CNF::from_rgbd(rgbd::Digest::new(digest.to_string()).read().unwrap());
            let solution = block_on(dpll(expr.clone()));
            assert!(solution.is_sat());
        }
    }

    #[test]
    fn test_dpll_solve_unsat() {
        const DATASET: [&str; 5] = [
            "2b738a1991a7318cad993a809b10cc2c",
            "18f54820956791d3028868b56a09c6cd",
            "00f969737ba4338bd233cd3ed249bd55",
            "38de0de52a209b6d0beb50986fd8b506",
            "04e47e6635908600ef3938b32644825a",
        ];
        for digest in DATASET {
            let expr = CNF::from_rgbd(rgbd::Digest::new(digest.to_string()).read().unwrap());
            let solution = block_on(dpll(expr.clone()));
            assert!(solution.is_unsat());
        }
    }
}
