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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Block {
    Start,
    Child(BlockId, Id),
    Merge(BlockId, BlockId),
    Return(BlockId, Id),
}

pub type DFG = EGraph<SSA, ()>;
pub type CFG = Vec<Block>;

#[derive(Debug, Clone)]
struct SSACtx<'a, 'b> {
    vars: FxHashMap<&'a str, Id>,
    dfg: &'b RefCell<DFG>,
    cfg: &'b RefCell<CFG>,
    block_hashcons: &'b RefCell<FxHashMap<Block, BlockId>>,
    last_block: BlockId,
}

pub fn optimistic_rewriting(func: &FuncAST) -> (DFG, CFG) {
    let dfg = RefCell::new(EGraph::new(()));
    let cfg = RefCell::new(CFG::default());
    let block_hashcons = RefCell::new(FxHashMap::default());

    let mut ctx = SSACtx {
        vars: FxHashMap::default(),
        dfg: &dfg,
        cfg: &cfg,
        block_hashcons: &block_hashcons,
        last_block: 0,
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
        if let Some(id) = self.block_hashcons.borrow().get(&block) {
            *id
        } else {
            let mut cfg = self.cfg.borrow_mut();
            let id = cfg.len();
            cfg.push(block);
            self.block_hashcons.borrow_mut().insert(block, id);
            id
        }
    }

    fn set_block(&self, block: Block, id: BlockId) {
        assert!(id < self.cfg.borrow().len());
        let old_block = self.cfg.borrow()[id];
        let old_id = self.block_hashcons.borrow_mut().remove(&old_block).unwrap();
        assert_eq!(old_id, id);
        self.cfg.borrow_mut()[id] = block;
        self.block_hashcons.borrow_mut().insert(block, id);
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
        let mut then_ctx = None;
        let mut else_ctx = None;

        if !self.is_always_false(true_cond) {
            let then_block = self.add_block(Block::Child(self.last_block, true_cond));
            let mut ctx = self.clone();
            ctx.last_block = then_block;
            then_ctx = ctx.handle_stmt(then_stmt);
        }

        if !self.is_always_false(false_cond) {
            let else_block = self.add_block(Block::Child(self.last_block, false_cond));
            let mut ctx = self.clone();
            ctx.last_block = else_block;
            else_ctx = ctx.handle_stmt(else_stmt);
        }

        match (then_ctx, else_ctx) {
            (Some(then_ctx), Some(else_ctx)) => {
                let block = self.add_block(Block::Merge(then_ctx.last_block, else_ctx.last_block));
                self.merge_vars(&then_ctx, &else_ctx, block);
                self.last_block = block;
                Some(self)
            }
            (ctx, None) | (None, ctx) => ctx,
        }
    }

    fn handle_while(mut self, cond: &ExprAST, stmt: &'a StmtAST) -> Option<Self> {
        todo!()
    }

    fn handle_return(self, expr: &ExprAST) -> Option<Self> {
        let value = self.handle_expr(expr);
        self.add_block(Block::Return(self.last_block, value));
        None
    }

    fn merge_vars(&mut self, a: &Self, b: &Self, block: BlockId) {
        for (name, a_value) in &a.vars {
            if let Some(b_value) = b.vars.get(name) {
                self.vars
                    .insert(name, self.mk(SSA::Phi(block, [*a_value, *b_value])));
            }
        }
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

    fn is_always_false(&self, value: Id) -> bool {
        self.mk(SSA::Constant(0)) == value
    }
}
