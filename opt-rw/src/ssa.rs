use core::cell::RefCell;
use core::mem::take;

use egg::{
    Analysis, DidMerge, EGraph, Id, Rewrite, Runner, SimpleScheduler, define_language, rewrite,
};
use rustc_hash::FxHashMap;

use crate::ast::{BinaryOp, ExprAST, FuncAST, StmtAST, UnaryOp};

pub type BlockId = usize;
type KnotId = usize;

define_language! {
    pub enum SSA {
        Constant(i64),
        Param(usize),
        Phi(BlockId, [Id; 2]),
        Unary(UnaryOp, Id),
        Binary(BinaryOp, [Id; 2]),
        Knot(KnotId),
    }
}

fn mk_rewrites() -> Vec<Rewrite<SSA, ConstantFolding>> {
    vec![
        rewrite!("comm-add"; "(Add ?a ?b)" => "(Add ?b ?a)"),
        rewrite!("comm-mul"; "(Mul ?a ?b)" => "(Mul ?b ?a)"),
        rewrite!("mul-1"; "(Mul ?a 1)" => "?a"),
        rewrite!("add-0"; "(Add ?a 0)" => "?a"),
        rewrite!("mul-0"; "(Mul ?a 0)" => "0"),
        rewrite!("mul-2"; "(Mul ?a 2)" => "(Add ?a ?a)"),
        rewrite!("not-ee"; "(Not (EE ?a ?b))" => "(NE ?a ?b)"),
        rewrite!("not-ne"; "(Not (NE ?a ?b))" => "(EE ?a ?b)"),
        rewrite!("ee-same"; "(EE ?a ?a)" => "1"),
        rewrite!("ne-same"; "(NE ?a ?a)" => "0"),
    ]
}

fn meet(a: Option<i64>, b: Option<i64>) -> Option<i64> {
    match (a, b) {
        (None, None) => None,
        (Some(m), None) | (None, Some(m)) => Some(m),
        (Some(a), Some(b)) => {
            assert_eq!(a, b);
            Some(a)
        }
    }
}

#[derive(Default)]
pub struct ConstantFolding;
impl Analysis<SSA> for ConstantFolding {
    type Data = Option<i64>;

    fn make(egraph: &mut EGraph<SSA, Self>, enode: &SSA, _id: Id) -> Self::Data {
        let c = |i: Id| egraph[i].data;
        use BinaryOp::*;
        use SSA::*;
        use UnaryOp::*;
        match enode {
            Constant(cons) => Some(*cons),
            Param(_) | Knot(_) => None,
            Phi(_, inputs) => meet(c(inputs[0]), c(inputs[1])),
            Unary(Neg, id) => c(*id).and_then(|cons| cons.checked_neg()),
            Unary(Not, id) => c(*id).map(|cons| if cons == 0 { 1 } else { 0 }),
            Binary(Add, inputs) => {
                c(inputs[0]).and_then(|lhs| c(inputs[1]).and_then(|rhs| lhs.checked_add(rhs)))
            }
            Binary(Sub, inputs) => {
                c(inputs[0]).and_then(|lhs| c(inputs[1]).and_then(|rhs| lhs.checked_sub(rhs)))
            }
            Binary(Mul, inputs) => {
                c(inputs[0]).and_then(|lhs| c(inputs[1]).and_then(|rhs| lhs.checked_mul(rhs)))
            }
            Binary(EE, inputs) => {
                c(inputs[0]).and_then(|lhs| c(inputs[1]).map(|rhs| (lhs == rhs) as i64))
            }
            Binary(NE, inputs) => {
                c(inputs[0]).and_then(|lhs| c(inputs[1]).map(|rhs| (lhs != rhs) as i64))
            }
            Binary(LT, inputs) => {
                c(inputs[0]).and_then(|lhs| c(inputs[1]).map(|rhs| (lhs < rhs) as i64))
            }
            Binary(LE, inputs) => {
                c(inputs[0]).and_then(|lhs| c(inputs[1]).map(|rhs| (lhs <= rhs) as i64))
            }
            Binary(GT, inputs) => {
                c(inputs[0]).and_then(|lhs| c(inputs[1]).map(|rhs| (lhs > rhs) as i64))
            }
            Binary(GE, inputs) => {
                c(inputs[0]).and_then(|lhs| c(inputs[1]).map(|rhs| (lhs >= rhs) as i64))
            }
        }
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
        let m = meet(*a, b);
        let d = DidMerge(*a != m, b != m);
        *a = m;
        d
    }

    fn modify(egraph: &mut EGraph<SSA, Self>, id: Id) {
        if let Some(cons) = egraph[id].data {
            let cons = egraph.add(SSA::Constant(cons));
            egraph.union(id, cons);
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

pub type DFG = EGraph<SSA, ConstantFolding>;
pub type CFG = Vec<Block>;
type KnotMap<'a> = FxHashMap<(BlockId, &'a str), KnotId>;

#[derive(Debug, Clone)]
struct SSACtx<'a, 'b> {
    vars: FxHashMap<&'a str, Id>,
    dfg: &'b RefCell<DFG>,
    cfg: &'b RefCell<CFG>,
    last_block: BlockId,
    knots: &'b RefCell<KnotMap<'a>>,
    rws: &'b Vec<Rewrite<SSA, ConstantFolding>>,
}

pub fn optimistic_rewriting(func: &FuncAST) -> (DFG, CFG) {
    let dfg = RefCell::new(EGraph::new(ConstantFolding));
    let cfg = RefCell::new(CFG::default());
    let knots = RefCell::new(KnotMap::default());

    let rws = mk_rewrites();
    let mut ctx = SSACtx {
        vars: FxHashMap::default(),
        dfg: &dfg,
        cfg: &cfg,
        last_block: 0,
        knots: &knots,
        rws: &rws,
    };
    for (idx, name) in func.params.iter().enumerate() {
        ctx.vars.insert(name, dfg.borrow_mut().add(SSA::Param(idx)));
    }
    ctx.last_block = ctx.add_block(Block::Start);
    ctx.handle_stmt(&func.body);

    cfg.borrow_mut().iter_mut().for_each(|block| match block {
        Block::Start | Block::Merge(_, _) => {}
        Block::Child(_, id) | Block::Return(_, id) => *id = dfg.borrow().find(*id),
    });
    (dfg.into_inner(), cfg.into_inner())
}

fn eqsat(egraph: &mut EGraph<SSA, ConstantFolding>, rws: &Vec<Rewrite<SSA, ConstantFolding>>) {
    let runner = Runner::<SSA, ConstantFolding, ()>::new(ConstantFolding)
        .with_iter_limit(10)
        .with_egraph(take(egraph))
        .with_scheduler(SimpleScheduler)
        .run(rws);
    *egraph = runner.egraph;
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

    fn knot(&self, block: BlockId, var: &'a str) -> KnotId {
        if let Some(id) = self.knots.borrow().get(&(block, var)) {
            *id
        } else {
            let id = self.knots.borrow().len();
            self.knots.borrow_mut().insert((block, var), id);
            id
        }
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
                self.add_block(Block::Start);
            let mut new_ctx = self.clone();
            ssa_intersection(&self.vars, &ctx.vars).for_each(|(name, _, _)| {
                new_ctx
                    .vars
                    .insert(name, self.mk(SSA::Knot(self.knot(header_block, name))));
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
                    let knot = self
                        .lookup(SSA::Knot(self.knot(header_block, name)))
                        .unwrap();
                    let phi = self.mk(SSA::Phi(header_block, [init_value, loop_value]));
                    self.union(knot, phi);
                    exit_ctx.vars.insert(name, self.find(knot));
                },
            );
            exit_ctx.last_block = header_block;
            self = exit_ctx;
        }

        let false_cond = self.mk(SSA::Unary(UnaryOp::Not, true_cond));
        if !self.is_always_false(false_cond) {
            let exit_block = self.add_block(Block::Child(self.last_block, false_cond));
            self.last_block = exit_block;
            Some(self)
        } else {
            None
        }
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

    fn mk(&self, value: SSA) -> Id {
        self.dfg.borrow_mut().add(value)
    }

    fn lookup(&self, value: SSA) -> Option<Id> {
        self.dfg.borrow_mut().lookup(value)
    }

    fn union(&self, a: Id, b: Id) {
        self.dfg.borrow_mut().union(a, b);
    }

    fn find(&self, id: Id) -> Id {
        self.dfg.borrow().find(id)
    }

    fn is_always_false(&self, value: Id) -> bool {
        eqsat(&mut self.dfg.borrow_mut(), self.rws);
        self.mk(SSA::Constant(0)) == self.find(value)
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
fn test(x) return x != 7;
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let (dfg, cfg) = optimistic_rewriting(&parsed[0]);

        use BinaryOp::*;
        use SSA::*;
        let x = dfg.lookup(Param(0)).unwrap();
        let seven = dfg.lookup(Constant(7)).unwrap();
        let ne = dfg.lookup(Binary(NE, [x, seven])).unwrap();

        use Block::*;
        assert_eq!(cfg, [Start, Return(0, ne)]);
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
        assert_eq!(
            cfg,
            [
                Start,
                Child(0, x),
                Child(0, not_x),
                Merge(1, 2),
                Return(3, x)
            ]
        );
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
        let phi = dfg.lookup(Knot(0)).unwrap();
        let not = dfg.lookup(Unary(Not, phi)).unwrap();

        use Block::*;
        assert_eq!(
            cfg,
            [
                Start,
                Merge(0, 2),
                Child(1, phi),
                Child(1, not),
                Return(3, phi)
            ]
        );
    }

    #[test]
    fn ssa5() {
        let program = r#"
fn test(x) { while x { return x + 1; } return x + 1; }
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let (dfg, cfg) = optimistic_rewriting(&parsed[0]);

        use BinaryOp::*;
        use SSA::*;
        use UnaryOp::*;
        let x = dfg.lookup(Param(0)).unwrap();
        let not_x = dfg.lookup(Unary(Not, x)).unwrap();
        let one = dfg.lookup(Constant(1)).unwrap();
        let add = dfg.lookup(Binary(Add, [x, one])).unwrap();

        use Block::*;
        assert_eq!(
            cfg,
            [
                Start,
                Child(0, x),
                Return(1, add),
                Child(0, not_x),
                Return(3, add)
            ]
        );
    }

    #[test]
    fn ssa6() {
        let program = r#"
fn test(x) { if 0 * x {  } else {  } return x; }
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let (dfg, cfg) = optimistic_rewriting(&parsed[0]);

        use SSA::*;
        use UnaryOp::*;
        let x = dfg.lookup(Param(0)).unwrap();
        let zero = dfg.lookup(Constant(0)).unwrap();
        let not = dfg.lookup(Unary(Not, zero)).unwrap();

        use Block::*;
        assert_eq!(cfg, [Start, Child(0, not), Return(1, x)]);
    }

    #[test]
    fn ssa7() {
        let program = r#"
fn test(x) { y = 2; while y { if y * x == x + x { return 7; } y = y + 1; } return y; }
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let (dfg, cfg) = optimistic_rewriting(&parsed[0]);

        use SSA::*;
        let one = dfg.lookup(Constant(1)).unwrap();
        let two = dfg.lookup(Constant(2)).unwrap();
        let seven = dfg.lookup(Constant(7)).unwrap();

        use Block::*;
        assert_eq!(
            cfg,
            [Start, Child(0, two), Child(1, one), Return(2, seven),]
        );
    }
}
