use core::cell::RefCell;

use egg::{define_language, EGraph, Id};
use rustc_hash::FxHashMap;

use crate::ast::{BinaryOp, ExprAST, FuncAST, StmtAST, UnaryOp};

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

pub type DFG = EGraph<SSA, ()>;
pub type CFG = Vec<Block>;

#[derive(Debug, Clone)]
struct SSACtx<'a, 'b> {
    vars: FxHashMap<&'a str, Id>,
    dfg: &'b RefCell<DFG>,
    cfg: &'b RefCell<CFG>,
    curr_block: BlockId,
}

pub fn optimistic_rewriting(func: &FuncAST) -> (DFG, CFG) {
    let dfg = RefCell::new(EGraph::new(()));
    let cfg = RefCell::new(CFG::default());

    let mut ctx = SSACtx {
        vars: FxHashMap::default(),
        dfg: &dfg,
        cfg: &cfg,
        curr_block: 0,
    };
    for (idx, name) in func.params.iter().enumerate() {
        ctx.vars.insert(name, dfg.borrow_mut().add(SSA::Param(idx)));
    }
    cfg.borrow_mut().push(Block::Start);
    ctx.handle_stmt(&func.body);

    (dfg.into_inner(), cfg.into_inner())
}

impl<'a, 'b> SSACtx<'a, 'b> {
    fn add_block(&self, block: Block) -> BlockId {
        let mut cfg = self.cfg.borrow_mut();
        let id = cfg.len();
        cfg.push(block);
        id
    }

    fn handle_stmt(self, stmt: &'a StmtAST) -> Option<Self> {
        use StmtAST::*;
        match stmt {
            Block(stmts) => self.handle_block(stmts),
            Assign(name, expr) => self.handle_assign(name, expr),
            IfElse(cond, then_stmt, else_stmt) => self.handle_ifelse(cond, then_stmt, else_stmt),
            While(cond, stmt) => self.handle_while(cond, stmt),
            Return(expr) => self.handle_return(expr),
        }
    }

    fn handle_block(mut self, stmts: &'a Vec<StmtAST>) -> Option<Self> {
        for stmt in stmts {
            if let Some(ctx) = self.handle_stmt(stmt) {
                self = ctx;
            } else {
                return None;
            }
        }
        Some(self)
    }

    fn handle_assign(mut self, name: &'a str, expr: &ExprAST) -> Option<Self> {
        let value = self.handle_expr(expr);
        self.vars.insert(name, value);
        Some(self)
    }

    fn handle_ifelse(
        mut self,
        cond: &ExprAST,
        then_stmt: &'a StmtAST,
        else_stmt: &'a StmtAST,
    ) -> Option<Self> {
        let true_cond = self.handle_expr(cond);
        let false_cond = self.mk(SSA::Unary(UnaryOp::Not, true_cond));
        let one = self.mk(SSA::Constant(1));

        todo!()
    }

    fn handle_while(mut self, cond: &ExprAST, stmt: &'a StmtAST) -> Option<Self> {
        todo!()
    }

    fn handle_return(self, expr: &ExprAST) -> Option<Self> {
        let value = self.handle_expr(expr);
        self.add_block(Block::Return(
            (self.curr_block, self.mk(SSA::Constant(1))),
            value,
        ));
        None
    }

    fn handle_expr(&self, expr: &ExprAST) -> Id {
        use ExprAST::*;
        let value = match expr {
            Number(cons) => SSA::Constant(*cons),
            Variable(name) => return self.vars[&name as &str],
            Unary(op, input) => SSA::Unary(*op, self.handle_expr(input)),
            Binary(op, lhs, rhs) => {
                SSA::Binary(*op, [self.handle_expr(lhs), self.handle_expr(rhs)])
            }
        };
        self.mk(value)
    }

    fn mk(&self, value: SSA) -> Id {
        self.dfg.borrow_mut().add(value)
    }
}
