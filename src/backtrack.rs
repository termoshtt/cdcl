mod status;

use crate::{pending_once, Literal, Solution, State, CNF};
use anyhow::{ensure, Context, Result};
use either::Either;
use status::*;
use std::{
    collections::{BTreeSet, HashMap},
    num::NonZeroU32,
};

/// Algorithm A in Knuth 4B, backtrack with double linked list
pub async fn backtrack(cnf: CNF) -> Solution {
    if cnf.is_conflicted() {
        return Solution::UnSat;
    }
    if cnf.is_tautology() {
        return Solution::Sat(State::default());
    }
    let mut solver = Solver::new(cnf).unwrap();
    solver.solve().await
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
    id_mapping: IdMapping,

    // `a`: The number of active clauses in the current state
    num_active_clauses: u32,
    // `m_d`: The status of each literal at depth `d`
    status: StatusStack,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct IdMapping(HashMap<NonZeroU32, usize>);

impl IdMapping {
    fn new(literals: &BTreeSet<NonZeroU32>) -> Self {
        Self(
            literals
                .into_iter()
                .enumerate()
                .map(|(new, &original)| (original, new))
                .collect(),
        )
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    #[allow(dead_code)]
    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn translate(&self, lit: Literal) -> u32 {
        2 * (self.0[&lit.id] as u32 + 1) + if lit.positive { 0 } else { 1 }
    }

    fn as_state(&self, stack: &StatusStack) -> State {
        self.0
            .iter()
            .map(|(&id, &d)| Literal {
                id,
                positive: stack.get(d).is_true(),
            })
            .collect()
    }
}

impl Solver {
    fn new(cnf: CNF) -> Result<Self> {
        // Mapping the literals to a contiguous range
        let id_mapping = IdMapping::new(&cnf.supp());

        // Head two dummy cells and special cells
        let head_size = 2 * id_mapping.len() + 2;
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
            let ls: Vec<_> = clause.literals().context("Conflicted clause")?.collect();
            for lit in ls.iter().rev() {
                cells.push(Cell {
                    literal: id_mapping.translate(**lit),
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

        Ok(Self {
            start,
            size,
            cells,
            id_mapping,
            num_active_clauses,
            status: StatusStack::default(),
        })
    }

    /// `2*n + 2`
    fn head_cell_size(&self) -> usize {
        *self.start.last().unwrap()
    }

    fn get_cell(&self, pos: u32) -> &Cell {
        &self.cells[pos as usize]
    }

    /// `C[l]`
    fn literal_size(&self, lit: u32) -> u32 {
        let cell = self.get_cell(lit);
        // Not the cell for clauses
        debug_assert_eq!(cell.literal, 0);
        cell.clause_id_or_size
    }

    fn get_status(&self) -> State {
        self.id_mapping.as_state(&self.status)
    }

    // A2: Select the literal
    fn select(&mut self) -> Either<Solution, u32> {
        let mut l = 2 * self.status.d();
        // if C[l] <= C[l+1] then l = l + 1
        if self.literal_size(l) <= self.literal_size(l + 1) {
            l += 1;
        }
        // m_d <- l&1 + 4[C(l^1) == 0]
        self.status.select(
            if self.literal_size(l ^ 1) != 0 {
                l & 1
            } else {
                (l & 1) + 4
            }
            .into(),
        );
        // If C[l] = a then return SAT
        if self.literal_size(l) == self.num_active_clauses {
            Either::Left(Solution::Sat(self.get_status()))
        } else {
            Either::Right(l)
        }
    }

    /// A3: remove ¬l from clauses
    /// - If empty clause is found, return false
    fn remove_negated(&mut self, l: u32) -> bool {
        let head_size = self.head_cell_size() as u32;
        let mut p = self.get_cell(l ^ 1).forward;
        while p >= head_size {
            debug_assert_eq!(self.get_cell(p).literal, l ^ 1);
            let clause_id = self.get_cell(p).clause_id_or_size;
            let size = self.size[clause_id as usize];
            debug_assert_ne!(size, 0, "This cell is not inactivated");
            if size == 1 {
                // This clause becomes empty by inactivating this cell
                // Start partial backtracking
                p = self.get_cell(p).backward;
                while p >= head_size {
                    let j = self.get_cell(p).clause_id_or_size;
                    self.size[j as usize] += 1;
                    p = self.get_cell(p).backward;
                }
                return false;
            }
            self.size[clause_id as usize] = size - 1;
            p = self.get_cell(p).forward;
        }
        true
    }

    /// A4: Inactivate clauses containing l
    fn inactivate(&mut self, l: u32) {
        let head_size = self.head_cell_size() as u32;
        let mut p = self.get_cell(l).forward;
        while p >= head_size {
            debug_assert_eq!(self.get_cell(p).literal, l);
            let j = self.get_cell(p).clause_id_or_size;
            // The last active cell of this clause must be `p`
            let start = self.start[j as usize];
            let end = start + self.size[j as usize] - 1;
            debug_assert_eq!(end as u32, p);
            // Remove cells in this clause from linked list
            for s in start..end {
                let f = self.cells[s].forward;
                let b = self.cells[s].backward;
                self.cells[f as usize].backward = b;
                self.cells[b as usize].forward = f;
                let q = self.cells[s].literal;
                debug_assert_ne!(q, l);
                debug_assert_ne!(q, 0);
                self.cells[q as usize].clause_id_or_size -= 1;
            }
            p = self.get_cell(p).forward;
        }
        self.num_active_clauses -= self.get_cell(l).clause_id_or_size;
    }

    /// A5: Try the next literal
    fn flip(&mut self) -> Option<u32> {
        self.status.flip()
    }

    /// A7: Reactivate clauses containing l
    fn reactivate(&mut self, l: u32) {
        self.num_active_clauses += self.get_cell(l).clause_id_or_size;
        let head_size = self.head_cell_size() as u32;
        let mut p = self.get_cell(l).backward;
        while p >= head_size {
            let j = self.get_cell(p).clause_id_or_size;
            let start = self.start[j as usize];
            let end = start + self.size[j as usize] - 1;
            for s in start..end {
                let f = self.cells[s].forward;
                let b = self.cells[s].backward;
                self.cells[f as usize].backward = s as u32;
                self.cells[b as usize].forward = s as u32;
                let q = self.cells[s].literal;
                self.cells[q as usize].clause_id_or_size += 1;
            }
            p = self.get_cell(p).backward;
        }
    }

    /// A8: Restore ¬l to clauses
    fn restore_negated(&mut self, l: u32) {
        let head_size = self.head_cell_size() as u32;
        let mut p = self.get_cell(l ^ 1).forward;
        while p >= head_size {
            let j = self.get_cell(p).clause_id_or_size;
            self.size[j as usize] += 1;
            p = self.get_cell(p).forward;
        }
    }

    async fn solve(&mut self) -> Solution {
        'a2: loop {
            pending_once().await;
            // A2
            let mut l = match self.select() {
                Either::Left(solution) => return solution,
                Either::Right(l) => l,
            };
            'a3: loop {
                pending_once().await;
                // A3
                if self.remove_negated(l) {
                    // A4
                    self.inactivate(l);
                    continue 'a2;
                }
                loop {
                    pending_once().await;
                    // A5
                    if let Some(flipped) = self.flip() {
                        l = flipped;
                        continue 'a3;
                    }
                    // A6: Backtrack
                    let Some(l) = self.status.backtrack() else {
                        return Solution::UnSat;
                    };
                    // A7: re-activate clauses containing l
                    self.reactivate(l);
                    // A8: restore ¬l to clauses
                    self.restore_negated(l);
                }
            }
        }
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
            prop_assert!(!solver.id_mapping.is_empty());
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

    #[test]
    fn test_solve() {
        for (expr, expected) in crate::testing::single_solution_cases() {
            assert_eq!(
                crate::timeout::block_on(backtrack(dbg!(expr).clone())),
                dbg!(expected),
            );
        }
    }

    #[test]
    fn test_90fd3ab118c483a7d99707384c6c6c0a() {
        use std::ops::Deref;
        let digest = rgbd::Digest::new("90fd3ab118c483a7d99707384c6c6c0a".to_string());

        // This is a known SAT instance
        let answer = rgbd::get_results()
            .unwrap()
            .get(digest.deref())
            .cloned()
            .unwrap();
        assert_eq!(answer, rgbd::SatResult::Sat);

        let expr = CNF::from_rgbd(digest.read().unwrap());
        let out = crate::timeout::block_on(backtrack(expr));
        if let Solution::Sat(state) = &out {
            dbg!(state);
        } else {
            panic!("Must be SAT");
        }
    }
}
