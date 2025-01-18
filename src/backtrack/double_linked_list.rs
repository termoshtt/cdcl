use crate::{Solution, State, CNF};
use anyhow::{ensure, Context, Result};
use either::Either;
use std::{collections::HashMap, num::NonZeroU32};

/// Algorithm A in Knuth 4B, backtrack with double linked list
pub async fn backtrack_a(cnf: CNF) -> Solution {
    let mut solver = Solver::new(cnf).unwrap();
    solver.solve()
}

/// Cell for each literal in clauses
#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct Cell {
    /// `L`: The literal in the cell. This is default value `0` for head cells.
    literal: u32,
    /// `F`: The forward pointer
    forward: u32,
    /// `B`: The backward pointer
    backward: u32,
    /// `C`: The clause id or the number of cells with the same literal
    clause_id_or_size: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Solver {
    start: Vec<usize>,
    size: Vec<usize>,
    cells: Vec<Cell>,
    /// The original literal IDs
    literals: HashMap<NonZeroU32, u32>,

    // `a`: The number of active clauses in the current state
    num_active_clauses: u32,
    // `d`: Implicit depth of the search tree + 1
    depth: u32,
    // `m_d`: The status of each literal at depth `d`
    status: HashMap<u32, Status>,
}

/// Search status for each literal
#[derive(Debug, Clone, PartialEq, Eq, Copy, PartialOrd, Ord)]
enum Status {
    /// Try `1` before trying `0`
    TryT = 0,
    /// Try `0` before trying `1`
    TryF = 1,
    /// Try `1` after trying `0` has failed
    TryTAfterF = 2,
    /// Try `0` after trying `1` has failed
    TryFAfterT = 3,
    /// Try `1` for the pure literal
    PureT = 4,
    /// Try `0` for the pure literal
    PureF = 5,
}

impl PartialEq<u32> for Status {
    fn eq(&self, other: &u32) -> bool {
        *self as u32 == *other
    }
}

impl PartialOrd<u32> for Status {
    fn partial_cmp(&self, other: &u32) -> Option<std::cmp::Ordering> {
        (*self as u32).partial_cmp(other)
    }
}

impl From<u32> for Status {
    fn from(value: u32) -> Self {
        match value {
            0 => Self::TryT,
            1 => Self::TryF,
            2 => Self::TryTAfterF,
            3 => Self::TryFAfterT,
            4 => Self::PureT,
            5 => Self::PureF,
            _ => unreachable!("Status out of range"),
        }
    }
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
        let num_active_clauses = size.iter().filter(|&&s| s > 0).count() as u32;
        ensure!(num_active_clauses > 0, "No active clauses");
        let depth = 1;

        Ok(Self {
            start,
            size,
            cells,
            literals,
            num_active_clauses,
            depth,
            status: HashMap::new(),
        })
    }

    fn head_cell_size(&self) -> usize {
        *self.start.last().unwrap()
    }

    fn get_cell(&self, pos: u32) -> &Cell {
        &self.cells[pos as usize]
    }

    fn get_cell_mut(&mut self, pos: u32) -> &mut Cell {
        &mut self.cells[pos as usize]
    }

    /// `C[l]`
    fn literal_size(&self, lit: u32) -> u32 {
        let cell = self.get_cell(lit);
        // Not the cell for clauses
        debug_assert_eq!(cell.literal, 0);
        cell.clause_id_or_size
    }

    fn get_state(&self) -> State {
        // x_j <- 1 ^ (m_j & 1)
        todo!()
    }

    // A2: Select the literal
    fn select(&mut self) -> Either<Solution, u32> {
        let mut l = 2 * self.depth;
        // if C[l] <= C[l^1] then l = l + 1
        if self.literal_size(l) <= self.literal_size(l + 1) {
            l += 1;
        }
        // m_d <- l&1 + 4[C(l^1) == 0]
        self.status.insert(
            self.depth,
            if self.literal_size(l ^ 1) == 0 {
                l & 1
            } else {
                l & 1 + 4
            }
            .into(),
        );
        // If C[l] = a then return SAT
        if self.literal_size(l) == self.num_active_clauses {
            Either::Left(Solution::Sat(self.get_state()))
        } else {
            Either::Right(l)
        }
    }

    pub fn solve(&mut self) -> Solution {
        let l = match self.select() {
            Either::Left(solution) => return solution,
            Either::Right(l) => l,
        };

        todo!()
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
