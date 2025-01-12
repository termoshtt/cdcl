//! Algorithm A (double linked list) in Knuth 4B

use crate::CNF;
use anyhow::{ensure, Context, Result};
use std::{collections::HashMap, num::NonZeroU32};

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
        let mut cells = (0..(2 * literals.len() + 2))
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

        // Linking the cells
        for pos in start[0]..cells.len() {
            let lit = cells[pos].literal;
            let f_pos = std::mem::replace(&mut cells[lit as usize].forward, pos as u32);
            cells[lit as usize].clause_id_or_size += 1;
            cells[f_pos as usize].backward = pos as u32;
            cells[pos].backward = lit;
            cells[pos].forward = f_pos;
        }

        Ok(Self {
            start,
            size,
            cells,
            literals,
        })
    }
}
