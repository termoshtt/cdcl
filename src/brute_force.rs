use crate::{take_minimal_id, CancelToken, Cancelable, Literal, Solution, CNF};

pub struct BruteForce {}

pub fn brute_force(input: CNF, cancel_token: CancelToken) -> Cancelable<Solution> {
    if let Some(solution) = input.is_solved() {
        return Ok(solution);
    }
    cancel_token.is_canceled()?;

    let fix = take_minimal_id(&input);
    for value in [true, false] {
        let lit = Literal {
            id: fix,
            positive: value,
        };
        log::trace!("Decision: {}", lit);
        let mut new = input.clone();
        new.substitute(lit);
        match brute_force(new, cancel_token.clone())? {
            Solution::Sat(mut state) => {
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
    fn test_brute_force() {
        for (expr, expected) in crate::testing::single_solution_cases() {
            assert_eq!(
                brute_force(expr.clone(), CancelToken::new()).unwrap(),
                expected,
                "Failed on {expr:?}",
            );
        }

        // x3 ∨ x4
        let mut expr = CNF::lit(3) | CNF::lit(4);
        let result = brute_force(expr.clone(), CancelToken::new()).unwrap();
        assert!(expr.evaluate(result.as_sat().unwrap()));
    }
}
