use core::cell::RefCell;
use core::mem::take;

use egg::{
    Analysis, DidMerge, EGraph, Id, Rewrite, Runner, SimpleScheduler, define_language, rewrite,
};
use rustc_hash::FxHashMap;

use crate::ast::{BinaryOp, ExprAST, FuncAST, StmtAST, UnaryOp};
use crate::interval::Interval;

pub type BlockId = usize;
// define_language!, as far as I can tell, doesn't appreciate multiple tuple fields being non-Id
// things. A KnotId corresponds to a tuple of a block, a variable name, and an interval. This also
// avoids needing a lifetime for the reference to the variable name.
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

fn mk_rewrites() -> Vec<Rewrite<SSA, IntervalAnalysis>> {
    vec![
        rewrite!("not-not-not"; "(Not (Not (Not ?a)))" => "(Not ?a)"),
        rewrite!("comm-add"; "(Add ?a ?b)" => "(Add ?b ?a)"),
        rewrite!("comm-mul"; "(Mul ?a ?b)" => "(Mul ?b ?a)"),
        rewrite!("add-0"; "(Add ?a 0)" => "?a"),
        rewrite!("sub-0"; "(Sub ?a 0)" => "?a"),
        rewrite!("sub-0-neg"; "(Sub 0 ?a)" => "(Neg ?a)"),
        rewrite!("sub-same"; "(Sub ?a ?a)" => "0"),
        rewrite!("mul-1"; "(Mul ?a 1)" => "?a"),
        rewrite!("mul-0"; "(Mul ?a 0)" => "0"),
        rewrite!("mul-2"; "(Mul ?a 2)" => "(Add ?a ?a)"),
        rewrite!("not-ee"; "(Not (EE ?a ?b))" => "(NE ?a ?b)"),
        rewrite!("not-ne"; "(Not (NE ?a ?b))" => "(EE ?a ?b)"),
        rewrite!("ee-same"; "(EE ?a ?a)" => "1"),
        rewrite!("ne-same"; "(NE ?a ?a)" => "0"),
    ]
}

// Simple interval analysis.
#[derive(Default)]
pub struct IntervalAnalysis {
    knot_intervals: Vec<Interval>,
}

impl Analysis<SSA> for IntervalAnalysis {
    type Data = Interval;

    fn make(egraph: &mut EGraph<SSA, Self>, enode: &SSA, _id: Id) -> Self::Data {
        let c = |i: Id| egraph[i].data;
        use SSA::*;
        match enode {
            Constant(cons) => Interval::from_constant(*cons),
            Param(_) => Interval::top(),
            Knot(id) => egraph.analysis.knot_intervals[*id],
            Phi(_, inputs) => c(inputs[0]).join(&c(inputs[1])),
            Unary(op, id) => c(*id).forward_unary(*op),
            Binary(op, inputs) => c(inputs[0]).forward_binary(&c(inputs[1]), *op),
        }
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
        let m = a.meet(&b);
        let d = DidMerge(*a != m, b != m);
        *a = m;
        d
    }

    fn modify(egraph: &mut EGraph<SSA, Self>, id: Id) {
        if let Some(cons) = egraph[id].data.try_constant() {
            let cons = egraph.add(SSA::Constant(cons));
            egraph.union(id, cons);
        }
    }
}

// CFG construction that is similar to the SSA form proposed in "Compiling with Abstract
// Interpretation". In particular, a control flow edge can only have a guard condition if it is the
// only incoming edge to a block. Note that the start block (entry point of the CFG) is always block
// ID 0. Sometimes, we set other block IDs to be Block::Start - these are either placeholders or
// blocks which are conceptually deleted.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Block {
    Start,
    Child(BlockId, Id),
    IfElseMerge(BlockId, BlockId),
    LoopMerge(BlockId, BlockId),
    Return(BlockId, Id),
}

pub type DFG = EGraph<SSA, IntervalAnalysis>;
pub type CFG = Vec<Block>;
// Intern pairs of blocks and variable names into KnotIds.
type KnotMap<'a> = FxHashMap<(BlockId, &'a str, Interval), KnotId>;

// The flow sensitive context used for building SSA. The main things the context holds are 1) a
// mapping of variables to e-class IDs and 2) the current block. The rest of the fields are
// references to shared flow insensitive constructs.
#[derive(Debug, Clone)]
struct SSACtx<'a, 'b> {
    vars: FxHashMap<&'a str, Id>,
    last_block: BlockId,

    dfg: &'b RefCell<DFG>,
    cfg: &'b RefCell<CFG>,
    knots: &'b RefCell<KnotMap<'a>>,
    rws: &'b Vec<Rewrite<SSA, IntervalAnalysis>>,
}

pub fn optimistic_rewriting(func: &FuncAST) -> (DFG, CFG) {
    let dfg = RefCell::new(EGraph::new(IntervalAnalysis {
        knot_intervals: vec![],
    }));
    let cfg = RefCell::new(CFG::default());
    let knots = RefCell::new(KnotMap::default());

    let rws = mk_rewrites();
    let mut ctx = SSACtx {
        vars: FxHashMap::default(),
        last_block: 0,
        dfg: &dfg,
        cfg: &cfg,
        knots: &knots,
        rws: &rws,
    };
    // The initial context starts at the start block and maps parameter variables to parameter nodes.
    for (idx, name) in func.params.iter().enumerate() {
        ctx.vars.insert(name, ctx.mk(SSA::Param(idx)));
    }
    ctx.last_block = ctx.add_block(Block::Start);
    ctx.handle_stmt(&func.body);
    // Explicitly perform equality saturation after the whole SSA program is built, since equality
    // saturation is only called when needed to characterize control flow while building.
    eqsat(&mut dfg.borrow_mut(), &rws);

    // Explicitly canonicalize the IDs in the CFG, since there's no guarantee that rewriting didn't
    // simplify guard conditions or returned values after the CFG was created.
    cfg.borrow_mut().iter_mut().for_each(|block| match block {
        Block::Start | Block::IfElseMerge(_, _) | Block::LoopMerge(_, _) => {}
        Block::Child(_, id) | Block::Return(_, id) => *id = dfg.borrow().find(*id),
    });
    (dfg.into_inner(), cfg.into_inner())
}

fn eqsat(egraph: &mut EGraph<SSA, IntervalAnalysis>, rws: &Vec<Rewrite<SSA, IntervalAnalysis>>) {
    let runner = Runner::<SSA, IntervalAnalysis, ()>::new(IntervalAnalysis::default())
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

    // Used to tie knots in the CFG.
    fn set_block(&self, block: Block, id: BlockId) {
        assert!(id < self.cfg.borrow().len());
        self.cfg.borrow_mut()[id] = block;
    }

    // Conceptually remove all blocks after a certain ID (inclusive). We don't re-use the IDs of the
    // removed blocks, since phis may have been created referencing removed blocks and we don't want
    // there to be confusion related to what block a phi refers to.
    fn remove_blocks(&self, first_to_remove: BlockId) {
        let len = self.cfg.borrow().len();
        for id in first_to_remove..len {
            self.set_block(Block::Start, id);
        }
    }

    // Intern a block ID, a variable name, and an interval into a knot.
    fn knot(&self, block: BlockId, var: &'a str, interval: Interval) -> KnotId {
        let knot = (block, var, interval);
        if let Some(id) = self.knots.borrow().get(&knot) {
            *id
        } else {
            let id = self.knots.borrow().len();
            self.knots.borrow_mut().insert(knot, id);
            self.dfg.borrow_mut().analysis.knot_intervals.push(interval);
            id
        }
    }

    // The handle_* functions for statements return an Option<SSACtx<'a, 'b>> to signal whether
    // control flow can possible reach *after* that statement (assuming the statement itself is
    // reachable). For example, handle_return always returns None, since control flow can never reach
    // right after a return statement. The handle_* functions are only ever called on statements
    // which are possibly reachable.

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

    // Control can flow after a block if control flow can flow after each statement in the block.
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

    // Control can always flow after an assignment.
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
        // Determine the known truthiness of the branch condition and its negation.
        let then_cond = self.handle_expr(cond);
        let else_cond = self.mk(SSA::Unary(UnaryOp::Not, then_cond));
        self.eqsat();
        let then_always_false = self.is_always_false(then_cond);
        let else_always_false = self.is_always_false(else_cond);

        // Execute the branch targets, only if they are reachable.
        let mut then_ctx = None;
        let mut else_ctx = None;
        if !then_always_false {
            let then_block = self.add_block(Block::Child(self.last_block, then_cond));
            let mut ctx = self.clone();
            ctx.last_block = then_block;
            then_ctx = ctx.handle_stmt(then_stmt);
        }
        if !else_always_false {
            let else_block = self.add_block(Block::Child(self.last_block, else_cond));
            let mut ctx = self.clone();
            ctx.last_block = else_block;
            else_ctx = ctx.handle_stmt(else_stmt);
        }

        // If control flow can reach after either branch, then control flow can reach after the if
        // else statement.
        match (then_ctx, else_ctx) {
            (Some(then_ctx), Some(else_ctx)) => {
                // Control flow can reach after both branches, so variables need to be merged with
                // phi nodes.
                let block =
                    self.add_block(Block::IfElseMerge(then_ctx.last_block, else_ctx.last_block));
                // Perform equality saturation to prevent spurious phis.
                self.eqsat();
                ssa_intersection(&then_ctx.vars, &else_ctx.vars, &self.dfg.borrow()).for_each(
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
        let mut then_cond = self.handle_expr(cond);
        // If the condition for the while is always false, then just ignore the while.
        self.eqsat();
        if self.is_always_false(then_cond) {
            return Some(self);
        }

        // Start by assuming that control flow cannot reach after the body of the while. In this
        // case, the while basically acts as an if else.
        let mut header_block = self.add_block(Block::Child(self.last_block, then_cond));
        let mut after_body_ctx = self.clone();
        after_body_ctx.last_block = header_block;

        if let Some(mut after_body_ctx) = after_body_ctx.handle_stmt(stmt) {
            // For widening and other conveniences, keep around the last intervals known at the
            // beginning of the loop for each variable that we will build a phi for.
            let mut previous_intervals: FxHashMap<&'a str, Interval> = FxHashMap::default();

            loop {
                let mut fixpoint_reached = true;
                self.eqsat();
                let differences: Vec<_> =
                    ssa_intersection(&self.vars, &after_body_ctx.vars, &self.dfg.borrow())
                        .collect();
                differences
                    .iter()
                    .for_each(|(name, init_value, loop_value)| {
                        let init_interval = self.interval(*init_value);
                        let loop_interval = self.interval(*loop_value);
                        let mut knot_interval = init_interval.join(&loop_interval);
                        // A fixpoint has been reached once the intervals derived for the variables
                        // at the loop header agree with the join of intervals from outside the loop
                        // and from the loop back edge.
                        if let Some(previous_interval) = previous_intervals.get(name) {
                            if *previous_interval != knot_interval {
                                knot_interval = previous_interval.widen(&knot_interval);
                                fixpoint_reached = false;
                            }
                        } else {
                            // Since previous_intervals starts out empty, the first iteration of the
                            // main loop will never reach a fixpoint. This is intended, since the
                            // loop needs to execute at least once to generate the body of the loop
                            // with knots and a header block for knot tying.
                            fixpoint_reached = false;
                        }
                        previous_intervals.insert(name, knot_interval);
                    });

                if fixpoint_reached {
                    // We only create phis once the interval on the knot is sound, since we don't
                    // index phis on the current interval (creating a phi too early would result in
                    // all future knots being equal, which is unsound).
                    differences
                        .iter()
                        .for_each(|(name, init_value, loop_value)| {
                            let knot = self
                                .lookup(SSA::Knot(self.knot(
                                    header_block,
                                    name,
                                    previous_intervals[name],
                                )))
                                .unwrap();
                            let phi = self.mk(SSA::Phi(header_block, [*init_value, *loop_value]));
                            self.union(knot, phi);
                            self.vars.insert(name, self.find(phi));
                        });
                    // Tie the knot in the CFG.
                    self.set_block(
                        Block::LoopMerge(self.last_block, after_body_ctx.last_block),
                        header_block,
                    );
                    self.last_block = header_block;
                    break;
                }

                // Re-execute the loop body with a new header block. Create knots with the desired
                // intervals for this iteration.
                self.remove_blocks(header_block);
                header_block = self.add_block(Block::Start);
                let mut new_ctx = self.clone();
                new_ctx.last_block = header_block;
                differences.iter().for_each(|(name, _, _)| {
                    new_ctx.vars.insert(
                        name,
                        self.mk(SSA::Knot(self.knot(
                            header_block,
                            name,
                            previous_intervals[name],
                        ))),
                    );
                });
                then_cond = new_ctx.handle_expr(cond);
                let new_body_block = self.add_block(Block::Child(header_block, then_cond));
                new_ctx.last_block = new_body_block;
                after_body_ctx = new_ctx.handle_stmt(stmt).unwrap();
            }
        }

        // At this point, self is always a context "at" the branching point for the loop. This is the
        // block preceding the loop if after the body is unreachable or the header of the loop if
        // after the body is reachable.
        let false_cond = self.mk(SSA::Unary(UnaryOp::Not, then_cond));
        // If the while condition is always true, then control flow cannot reach after the while.
        self.eqsat();
        if self.is_always_false(false_cond) {
            None
        } else {
            let exit_block = self.add_block(Block::Child(self.last_block, false_cond));
            self.last_block = exit_block;
            Some(self)
        }
    }

    fn handle_return(self, expr: &ExprAST) -> Option<Self> {
        let value = self.handle_expr(expr);
        self.add_block(Block::Return(self.last_block, value));
        None
    }

    // Convert expressions into e-class IDs - this is where variables are looked up in the flow
    // sensitive mapping from variables to e-class IDs.
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

    fn interval(&self, id: Id) -> Interval {
        self.dfg.borrow()[id].data
    }

    fn eqsat(&self) {
        eqsat(&mut self.dfg.borrow_mut(), self.rws);
    }

    fn is_always_false(&self, value: Id) -> bool {
        self.interval(value).is_cons(0)
    }
}

// Helper to iterate through variables whose e-class IDs differ among SSA contexts at control flow
// merge points.
fn ssa_intersection<'a, 'b>(
    a: &'a FxHashMap<&'b str, Id>,
    b: &'a FxHashMap<&'b str, Id>,
    egraph: &'a DFG,
) -> impl Iterator<Item = (&'b str, Id, Id)> + 'a {
    a.into_iter().filter_map(|(name, a_value)| {
        if let Some(b_value) = b.get(name)
            && egraph.find(*a_value) != egraph.find(*b_value)
        {
            Some((*name, egraph.find(*a_value), egraph.find(*b_value)))
        } else {
            None
        }
    })
}

#[cfg(test)]
mod tests {
    use crate::grammar::ProgramParser;

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
                IfElseMerge(1, 2),
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
fn test() { x = -5; while x { x = x + (1 * 3); } return x; }
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let (dfg, cfg) = optimistic_rewriting(&parsed[0]);

        let Some(Block::Return(_, id)) = cfg.last() else {
            panic!()
        };
        assert_eq!(dfg[*id].data, Interval::from_low(-5));
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
