use crate::{Expr, State, CNF};

pub fn take_minimal_id(cnf: &CNF) -> usize {
    assert!(cnf.as_bool().is_none());
    *cnf.variables()
        .first()
        .expect("Non-boolean CNF expression must have at least one variable.")
}

pub fn brute_force(input: CNF, selector: fn(&CNF) -> usize) -> Option<State> {
    match *input.as_expr() {
        // Already solved
        Expr::True => return Some(State::default()),
        // Never feasible
        Expr::False => return None,
        _ => {}
    }
    let fix = selector(&input);
    for value in [true, false] {
        log::trace!("Set x{} = {}", fix, value);
        if let Some(mut state) = brute_force(input.substitute(fix, value), selector) {
            state.insert(fix, value);
            return Some(state);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use maplit::btreemap;

    #[test]
    fn test_brute_force() {
        // True
        assert_eq!(
            brute_force(CNF::from(true), take_minimal_id),
            Some(State::default())
        );
        // False
        assert_eq!(brute_force(CNF::from(false), take_minimal_id), None);

        // x3
        assert_eq!(
            brute_force(CNF::variable(3), take_minimal_id),
            Some(btreemap! { 3 => true })
        );
        // ¬x3
        assert_eq!(
            brute_force(!CNF::variable(3), take_minimal_id),
            Some(btreemap! { 3 => false })
        );

        // x3 ∧ x4
        assert_eq!(
            brute_force(CNF::variable(3) & CNF::variable(4), take_minimal_id),
            Some(btreemap! { 3 => true, 4 => true })
        );
        // x3 ∧ ¬x4
        assert_eq!(
            brute_force(!CNF::variable(3) & CNF::variable(4), take_minimal_id),
            Some(btreemap! { 3 => false, 4 => true })
        );
        // ¬x3 ∧ x4
        assert_eq!(
            brute_force(!CNF::variable(3) & !CNF::variable(4), take_minimal_id),
            Some(btreemap! { 3 => false, 4 => false })
        );

        // x3 ∧ x4 ∧ x5
        assert_eq!(
            brute_force(
                CNF::variable(3) & CNF::variable(4) & CNF::variable(5),
                take_minimal_id
            ),
            Some(btreemap! { 3 => true, 4 => true, 5 => true })
        );

        // x3 ∨ x4
        let expr = CNF::variable(3) | CNF::variable(4);
        let result = brute_force(expr.clone(), take_minimal_id).unwrap();
        assert_eq!(expr.evaluate(&result), Expr::True);
    }
}
