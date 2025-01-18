use crate::{Solution, CNF};
use anyhow::{ensure, Context, Result};
use std::{collections::HashMap, num::NonZeroU32};

/// Algorithm A in Knuth 4B, backtrack with double linked list
pub async fn backtrack_a(cnf: CNF) -> Solution {
    let _solver = Solver::new(cnf).unwrap();
    todo!()
}

/// Cell for each literal in clauses
#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct Cell {
    /// The literal in the cell. This is default value `0` for head cells.
    literal: u32,
    /// The forward pointer
    forward: u32,
    /// The backward pointer
    backward: u32,
    /// The clause id or the number of cells with the same literal
    clause_id_or_size: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Solver {
    start: Vec<usize>,
    size: Vec<usize>,
    cells: Vec<Cell>,
    /// The original literal IDs
    literals: HashMap<NonZeroU32, u32>,

    // The current state
    num_active_clauses: usize,
    depth: usize,
}

impl Solver {
    fn new(cnf: CNF) -> Result<Self> {
        // Mapping the literals to a contiguous range
        let literals: HashMap<NonZeroU32, u32> = cnf
            .supp()
            .into_iter()
            .enumerate()
            .map(|(new, original)| (original, new as u32 + 1)) // New ID starts with 1
            .collect();

        // Head two dummy cells and special cells
        let head_size = 2 * literals.len() + 2;
        let mut cells = (0..head_size)
            .map(|i| {
                if i < 2 {
                    // Dummy cells
                    Cell::default()
                } else {
                    // Special cells
                    Cell {
                        // There are only this cell with the literal
                        forward: i as u32,
                        backward: i as u32,
                        ..Default::default()
                    }
                }
            })
            .collect::<Vec<Cell>>();

        // Cells for clauses
        // Note that clauses and literals are reversed since the algorithm fixes from smaller literals
        let clauses = cnf.clauses().context("Conflicted CNF")?;
        ensure!(!clauses.is_empty(), "Empty CNF");
        let mut start = vec![0; clauses.len()];
        let mut size = vec![0; clauses.len()];
        for (id, clause) in clauses.iter().enumerate().rev() {
            start[id] = cells.len();
            for lit in clause.literals().context("Conflicted clause")?.rev() {
                cells.push(Cell {
                    literal: 2 * literals[&lit.id] + if lit.positive { 0 } else { 1 },
                    clause_id_or_size: id as u32,
                    ..Default::default()
                });
            }
            size[id] = cells.len() - start[id];
        }
        ensure!(cells.len() < u32::MAX as usize, "Too many cells");

        // Linking the cells
        for pos in head_size..cells.len() {
            let lit = cells[pos].literal;
            let f_pos = std::mem::replace(&mut cells[lit as usize].forward, pos as u32);
            cells[lit as usize].clause_id_or_size += 1;
            cells[f_pos as usize].backward = pos as u32;
            cells[pos].backward = lit;
            cells[pos].forward = f_pos;
        }

        // A1: Initialize the state
        let num_active_clauses = size.iter().filter(|&&s| s > 0).count();
        ensure!(num_active_clauses > 0, "No active clauses");
        let depth = 1;

        Ok(Self {
            start,
            size,
            cells,
            literals,
            num_active_clauses,
            depth,
        })
    }

    fn head_cell_size(&self) -> usize {
        *self.start.last().unwrap()
    }

    fn get_cell(&self, pos: u32) -> &Cell {
        &self.cells[pos as usize]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn test_solver_init(cnf in CNF::arbitrary()) {
            // If the CNF is conflicted or tautology, the solver should return an error
            let conflicted = cnf.is_conflicted();
            let is_tautology = cnf.is_tautology();
            let solver = super::Solver::new(cnf);
            if conflicted || is_tautology {
                prop_assert!(solver.is_err());
                return Ok(());
            }

            // Otherwise, the solver should return a valid solver, and the fields should not be empty
            let solver = solver.unwrap();
            prop_assert!(!solver.start.is_empty());
            prop_assert!(!solver.size.is_empty());
            prop_assert!(!solver.literals.is_empty());
            // 2 dummy cells, at least 1 special cell, and at least 1 clause cell
            prop_assert!(solver.cells.len() >= 4);

            // Clause of smaller ID should have larger start
            for i in 0..solver.start.len() -1 {
                prop_assert!(solver.start[i] > solver.start[i + 1]);
            }

            // Head cells
            prop_assert_eq!(solver.get_cell(0), &Cell::default());
            prop_assert_eq!(solver.get_cell(1), &Cell::default());
            let head_size = solver.head_cell_size() as u32;
            prop_assert!(head_size >= 3);
            for pos in 2..head_size {
                let cell = solver.get_cell(pos);
                prop_assert_eq!(cell.literal, 0, "Head cells at {} should have 0 literal", pos);
                prop_assert!(cell.forward < solver.cells.len() as u32);
                prop_assert!(cell.backward < solver.cells.len() as u32);
                match (cell.forward >= head_size, cell.backward >= head_size) {
                    (true, true) => {
                        // Linked cell exists
                        let f = &solver.get_cell(cell.forward);
                        let b = &solver.get_cell(cell.backward);
                        prop_assert_eq!(f.literal, pos);
                        prop_assert_eq!(b.literal, pos);
                        prop_assert!(cell.clause_id_or_size > 0);
                    }
                    (false, false) => {
                        // No linked cells
                        prop_assert_eq!(cell.forward, pos);
                        prop_assert_eq!(cell.backward, pos);
                        prop_assert!(cell.clause_id_or_size == 0);
                    }
                    _ => {
                        prop_assert!(false, "Linked list is broken");
                    }
                }
            }

            // Traverse the cells in forward direction
            for lit in 2..head_size {
                let mut pos = lit;
                let mut current = solver.get_cell(lit);
                let size = current.clause_id_or_size;
                let mut count = 0;
                loop {
                    let next = solver.get_cell(current.forward);
                    prop_assert_eq!(next.backward, pos);
                    if current.literal != 0 {
                        prop_assert!(current.forward < pos)
                    }
                    if next.literal != 0 {
                        prop_assert_eq!(next.literal, lit);
                    }
                    pos = current.forward;
                    current = next;
                    if current.literal == 0 {
                        break;
                    }
                    count += 1;
                }
                prop_assert_eq!(count, size, "Count of literal {} mismatch", lit);
            }

            // Traverse the cells in backward direction
            for lit in 2..head_size {
                let mut pos = lit;
                let mut current = solver.get_cell(lit);
                let size = current.clause_id_or_size;
                let mut count = 0;
                loop {
                    let next = solver.get_cell(current.backward);
                    prop_assert_eq!(next.forward, pos);
                    if current.literal != 0 {
                        prop_assert!(current.backward < pos)
                    }
                    if next.literal != 0 {
                        prop_assert_eq!(next.literal, lit);
                    }
                    pos = current.backward;
                    current = next;
                    if current.literal == 0 {
                        break;
                    }
                    count += 1;
                }
                prop_assert_eq!(count, size, "Count of literal {} mismatch", lit);
            }
        }
    }
}
