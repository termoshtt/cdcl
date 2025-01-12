//! Algorithm A (double linked list) in Knuth 4B

use crate::CNF;
use anyhow::{Context, Result};
use std::{collections::HashMap, num::NonZeroU32};

/// Cell for each literal in clauses
#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct Cell {
    /// The literal in the cell
    literal: u32,
    /// The forward pointer
    forward: u32,
    /// The backward pointer
    backward: u32,
    /// The clause id
    clause_id: u32,
}

struct Solver {
    start: Vec<usize>,
    size: Vec<usize>,
    cells: Vec<Cell>,
    /// The original literal IDs
    literals: HashMap<NonZeroU32, u32>,
}

impl Solver {
    fn new(cnf: CNF) -> Result<Self> {
        // Mapping the literals to a contiguous range
        let literals: HashMap<NonZeroU32, u32> = cnf
            .supp()
            .into_iter()
            .enumerate()
            .map(|(base, new)| (new, base as u32))
            .collect();

        // Head two dummy cells and special cells
        let mut cells = vec![Cell::default(); 2 * (literals.len() + 1)];

        // Cells for clauses
        let clauses = cnf.clauses().context("Conflicted CNF")?;
        let mut start = vec![0; clauses.len()];
        let mut size = vec![0; clauses.len()];
        for (id, clause) in clauses.iter().enumerate().rev() {
            start[id] = cells.len();
            for lit in clause.literals().context("Conflicted clause")?.rev() {
                cells.push(Cell {
                    literal: 2 * literals[&lit.id] + if lit.positive { 0 } else { 1 },
                    clause_id: id as u32,
                    ..Default::default()
                });
            }
            size[id] = cells.len() - start[id];
        }

        // TODO: Fill the forward and backward pointers

        Ok(Self {
            start,
            size,
            cells,
            literals,
        })
    }
}
