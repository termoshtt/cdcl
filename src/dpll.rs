use crate::{pending_once, take_minimal_id, Literal, Solution, State, CNF};

async fn unit_propagation(input: &mut CNF, state: &mut State) {
    loop {
        pending_once().await;
        let units = input.take_unit_clauses();
        if units.is_empty() {
            return;
        }
        for lit in units {
            if input.substitute(lit).is_err() {
                return;
            }
            state.insert(lit);
        }
    }
}

pub async fn dpll(input: CNF) -> Solution {
    let mut stack = vec![(input, State::default())];
    while let Some((mut input, mut state)) = stack.pop() {
        unit_propagation(&mut input, &mut state).await;
        match input.is_solved() {
            Some(Solution::Sat(..)) => return Solution::Sat(state),
            Some(Solution::UnSat) => continue,
            _ => {}
        }

        // Make a decision
        let id = take_minimal_id(&input);
        let lit = Literal {
            id,
            positive: false,
        };
        let (mut input_, mut state_) = (input.clone(), state.clone());
        if input_.substitute(lit).is_ok() {
            state_.insert(lit);
            stack.push((input_, state_));
        }
        if input.substitute(!lit).is_ok() {
            state.insert(!lit);
            stack.push((input, state));
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
