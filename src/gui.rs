#![allow(unused_imports, dead_code)]
use crate::cnf::{Clause, Literal};

use std::num::NonZeroU32;

#[derive(Debug)]
struct Position {
    x: f32,
    y: f32,
}

pub struct GClauseId(pub NonZeroU32);

#[derive(Debug)]
struct GClause {
    clause: Clause,
    position: Position,
}
