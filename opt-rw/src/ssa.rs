use core::cell::RefCell;
use core::mem::{Discriminant, discriminant};
use core::slice::{from_mut, from_ref};

use egg::{EGraph, Id, Language};
use rustc_hash::FxHashMap;

use crate::ast::{BinaryOp, ExprAST, FuncAST, StmtAST, UnaryOp};

pub type BlockId = usize;

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub enum SSA<'a> {
    Constant(i64),
    Param(usize),
    Phi(BlockId, [Id; 2]),
    Unary(UnaryOp, Id),
    Binary(BinaryOp, [Id; 2]),
    Knot(BlockId, &'a str),
}

impl<'a> Language for SSA<'a> {
    type Discriminant = Discriminant<SSA<'a>>;

    fn discriminant(&self) -> Self::Discriminant {
        discriminant(self)
    }

    fn matches(&self, other: &Self) -> bool {
        use SSA::*;
        match (self, other) {
            (Constant(a), Constant(b)) if a == b => true,
            (Param(a), Param(b)) if a == b => true,
            (Phi(a, _), Phi(b, _)) if a == b => true,
            (Unary(a, _), Unary(b, _)) if a == b => true,
            (Binary(a, _), Binary(b, _)) if a == b => true,
            (Knot(a1, a2), Knot(b1, b2)) if a1 == b1 && a2 == b2 => true,
            _ => false,
        }
    }

    fn children(&self) -> &[Id] {
        use SSA::*;
        match self {
            Constant(_) | Param(_) | Knot(_, _) => &[],
            Phi(_, ids) | Binary(_, ids) => ids,
            Unary(_, id) => from_ref(id),
        }
    }

    fn children_mut(&mut self) -> &mut [Id] {
        use SSA::*;
        match self {
            Constant(_) | Param(_) | Knot(_, _) => &mut [],
            Phi(_, ids) | Binary(_, ids) => ids,
            Unary(_, id) => from_mut(id),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Block {
    Start,
    Child(BlockId, Id),
    Merge(BlockId, BlockId),
    Return(BlockId, Id),
}

pub type DFG<'a> = EGraph<SSA<'a>, ()>;
pub type CFG = Vec<Block>;

#[derive(Debug, Clone)]
struct SSACtx<'a, 'b> {
    vars: FxHashMap<&'a str, Id>,
    dfg: &'b RefCell<DFG<'a>>,
    cfg: &'b RefCell<CFG>,
    last_block: BlockId,
}

pub fn optimistic_rewriting(func: &FuncAST) -> (DFG<'_>, CFG) {
    let dfg = RefCell::new(EGraph::new(()));
    let cfg = RefCell::new(CFG::default());

    let mut ctx = SSACtx {
        vars: FxHashMap::default(),
        dfg: &dfg,
        cfg: &cfg,
        last_block: 0,
    };
    for (idx, name) in func.params.iter().enumerate() {
        ctx.vars.insert(name, dfg.borrow_mut().add(SSA::Param(idx)));
    }
    ctx.last_block = ctx.add_block(Block::Start);
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

    fn set_block(&self, block: Block, id: BlockId) {
        assert!(id < self.cfg.borrow().len());
        self.cfg.borrow_mut()[id] = block;
    }

    fn remove_blocks(&self, first_to_remove: BlockId) {
        self.cfg.borrow_mut().truncate(first_to_remove);
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
                ssa_intersection(&then_ctx.vars, &else_ctx.vars).for_each(
                    |(name, then_value, else_value)| {
                        self.vars
                            .insert(name, self.mk(SSA::Phi(block, [then_value, else_value])));
                    },
                );
                self.last_block = block;
                Some(self)
            }
            (ctx, None) | (None, ctx) => ctx,
        }
    }

    fn handle_while(mut self, cond: &ExprAST, stmt: &'a StmtAST) -> Option<Self> {
        let mut true_cond = self.handle_expr(cond);
        if self.is_always_false(true_cond) {
            return Some(self);
        }

        let body_block = self.add_block(Block::Child(self.last_block, true_cond));
        let mut ctx = self.clone();
        ctx.last_block = body_block;

        if let Some(ctx) = ctx.handle_stmt(stmt) {
            self.remove_blocks(body_block);
            let header_block =
                self.add_block(Block::Child(self.last_block, self.mk(SSA::Constant(1))));
            let mut new_ctx = self.clone();
            ssa_intersection(&self.vars, &ctx.vars).for_each(|(name, _, _)| {
                new_ctx
                    .vars
                    .insert(name, self.mk(SSA::Knot(header_block, name)));
            });
            true_cond = new_ctx.handle_expr(cond);
            let new_body_block = self.add_block(Block::Child(header_block, true_cond));
            new_ctx.last_block = new_body_block;
            let new_ctx = new_ctx.handle_stmt(stmt).unwrap();

            self.set_block(
                Block::Merge(self.last_block, new_ctx.last_block),
                header_block,
            );
            let mut exit_ctx = self.clone();
            ssa_intersection(&self.vars, &new_ctx.vars).for_each(
                |(name, init_value, loop_value)| {
                    let knot = self.lookup(SSA::Knot(header_block, name)).unwrap();
                    let phi = self.mk(SSA::Phi(header_block, [init_value, loop_value]));
                    self.union(knot, phi);
                    exit_ctx.vars.insert(name, self.find(knot));
                },
            );
            exit_ctx.last_block = header_block;
            self = exit_ctx;
        }

        let false_cond = self.mk(SSA::Unary(UnaryOp::Not, true_cond));
        let exit_block = self.add_block(Block::Child(self.last_block, false_cond));
        self.last_block = exit_block;
        Some(self)
    }

    fn handle_return(self, expr: &ExprAST) -> Option<Self> {
        let value = self.handle_expr(expr);
        self.add_block(Block::Return(self.last_block, value));
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

    fn mk(&self, value: SSA<'a>) -> Id {
        self.dfg.borrow_mut().add(value)
    }

    fn lookup(&self, value: SSA<'a>) -> Option<Id> {
        self.dfg.borrow_mut().lookup(value)
    }

    fn union(&self, a: Id, b: Id) {
        self.dfg.borrow_mut().union(a, b);
    }

    fn find(&self, id: Id) -> Id {
        self.dfg.borrow().find(id)
    }

    fn is_always_false(&self, value: Id) -> bool {
        self.mk(SSA::Constant(0)) == value
    }
}

fn ssa_intersection<'a, 'b>(
    a: &'a FxHashMap<&'b str, Id>,
    b: &'a FxHashMap<&'b str, Id>,
) -> impl Iterator<Item = (&'b str, Id, Id)> + 'a {
    a.into_iter().filter_map(|(name, a_value)| {
        if let Some(b_value) = b.get(name)
            && a_value != b_value
        {
            Some((*name, *a_value, *b_value))
        } else {
            None
        }
    })
}

mod tests {
    #[allow(unused_imports)]
    use crate::grammar::ProgramParser;

    #[allow(unused_imports)]
    use super::*;
    
    #[test]
    fn ssa1() {
        let program = r#"
fn test(x) return x;
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let (dfg, cfg) = optimistic_rewriting(&parsed[0]);

        use SSA::*;
        let id = dfg.lookup(Param(0)).unwrap();

        use Block::*;
        assert_eq!(cfg, [Start, Return(0, id)]);
    }
    
    #[test]
    fn ssa2() {
        let program = r#"
fn test(x) { if x {  } else {  } return x; }
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let (dfg, cfg) = optimistic_rewriting(&parsed[0]);

        use SSA::*;
        use UnaryOp::*;
        let x = dfg.lookup(Param(0)).unwrap();
        let not_x = dfg.lookup(Unary(Not, x)).unwrap();

        use Block::*;
        assert_eq!(cfg, [Start, Child(0, x), Child(0, not_x), Merge(1, 2), Return(3, x)]);
    }
    
    #[test]
    fn ssa3() {
        let program = r#"
fn test(x) { if 0 { } else { return x; } }
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let (dfg, cfg) = optimistic_rewriting(&parsed[0]);

        use SSA::*;
        use UnaryOp::*;
        let x = dfg.lookup(Param(0)).unwrap();
        let zero = dfg.lookup(Constant(0)).unwrap();
        let not_zero = dfg.lookup(Unary(Not, zero)).unwrap();

        use Block::*;
        assert_eq!(cfg, [Start, Child(0, not_zero), Return(1, x)]);
    }
    
    #[test]
    fn ssa4() {
        let program = r#"
fn test(x) { while x { x = x + 1; } return x; }
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let (dfg, cfg) = optimistic_rewriting(&parsed[0]);

        use SSA::*;
        use UnaryOp::*;
        let phi = dfg.lookup(Knot(1, "x")).unwrap();
        let not = dfg.lookup(Unary(Not, phi)).unwrap();

        use Block::*;
        assert_eq!(cfg, [Start, Merge(0, 2), Child(1, phi), Child(1, not), Return(3, phi)]);
    }
    
    #[test]
    fn ssa5() {
        let program = r#"
fn test(x) { while x { return x + 1; } return x + 1; }
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let (dfg, cfg) = optimistic_rewriting(&parsed[0]);

        use SSA::*;
        use BinaryOp::*;
        use UnaryOp::*;
        let x = dfg.lookup(Param(0)).unwrap();
        let not_x = dfg.lookup(Unary(Not, x)).unwrap();
        let one = dfg.lookup(Constant(1)).unwrap();
        let add = dfg.lookup(Binary(Add, [x, one])).unwrap();

        use Block::*;
        assert_eq!(cfg, [Start, Child(0, x), Return(1, add), Child(0, not_x), Return(3, add)]);
    }
}
