//! Algorithm A (double linked list) in Knuth 4B

use crate::Literal;

/// Cell for each literal in clauses
struct Cell {
    /// The literal in the cell
    literal: Literal,
    /// The forward pointer
    forward: usize,
    backward: usize,
    clause_id: usize,
}

struct Solver {
    start: Vec<usize>,
    size: Vec<usize>,
    cells: Vec<Cell>,
}
