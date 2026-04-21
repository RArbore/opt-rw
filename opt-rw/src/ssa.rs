use core::cell::RefCell;

use egg::{define_language, EGraph, Id};
use rustc_hash::FxHashMap;

use crate::ast::{BinaryOp, FuncAST, UnaryOp};

pub type BlockId = usize;

define_language! {
    pub enum SSA {
        Constant(i64),
        Param(usize),
        Phi(BlockId, [Id; 2]),
        Unary(UnaryOp, Id),
        Binary(BinaryOp, [Id; 2]),
    }
}

pub type Edge = (BlockId, Id);

#[derive(Debug, Clone)]
pub enum Block {
    Start,
    Child(Edge),
    Merge(Edge, Edge),
    Return(Edge, Id),
}

pub type CFG = Vec<Block>;

#[derive(Debug, Clone)]
struct SSACtx<'a, 'b> {
    vars: FxHashMap<&'a str, Id>,
    cfg: &'b RefCell<CFG>,
}

pub fn optimistic_rewriting(func: &FuncAST) -> (EGraph<SSA, ()>, CFG) {
    todo!()
}
