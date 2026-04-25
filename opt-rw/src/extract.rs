use core::cmp::Ordering;
use std::collections::BinaryHeap;

use egg::{Analysis, EGraph, Id, Language};
use rustc_hash::{FxHashMap, FxHashSet};

#[derive(Debug, Clone, PartialEq, Eq)]
struct QueueElement<L: Language> {
    node: L,
    cost: u128,
}

impl<L: Language> Ord for QueueElement<L> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        other
            .cost
            .cmp(&self.cost)
            .then_with(|| self.node.cmp(&other.node))
    }
}

impl<L: Language> PartialOrd for QueueElement<L> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

pub type Extraction<L> = FxHashMap<Id, (u128, L)>;

pub fn extract<L, A, F>(egraph: &EGraph<L, A>, cf: F) -> Extraction<L>
where
    L: Language,
    A: Analysis<L>,
    F: Fn(&L, &Extraction<L>) -> u128,
{
    let mut costs: Extraction<L> = Extraction::default();
    let mut priority: BinaryHeap<QueueElement<L>> = BinaryHeap::new();
    let mut parents: FxHashMap<Id, Vec<L>> = FxHashMap::default();
    let mut num_unknown_children: FxHashMap<L, usize> = FxHashMap::default();

    let mut child_dedup: FxHashSet<Id> = FxHashSet::default();
    for class in egraph.classes() {
        for node in class.iter() {
            node.for_each(|child| {
                child_dedup.insert(child);
            });
            num_unknown_children.insert(node.clone(), child_dedup.len());
            for child in child_dedup.drain() {
                parents.entry(child).or_default().push(node.clone());
            }

            if node.is_leaf() {
                let cost = cf(&node, &costs);
                priority.push(QueueElement {
                    node: node.clone(),
                    cost,
                });
            }
        }
    }

    while let Some(QueueElement { node, cost }) = priority.pop() {
        let id = egraph.lookup(node.clone()).unwrap();
        if costs.contains_key(&id) {
            continue;
        }

        assert_eq!(cost, cf(&node, &costs));
        costs.insert(id, (cost, node));
        for parent in parents.entry(id).or_default() {
            if costs.contains_key(&egraph.lookup(parent.clone()).unwrap()) {
                continue;
            }

            let num_unknown = num_unknown_children.get_mut(parent).unwrap();
            *num_unknown -= 1;
            if *num_unknown == 0 {
                let cost = cf(parent, &costs);
                priority.push(QueueElement {
                    node: parent.clone(),
                    cost,
                })
            }
        }
    }

    costs
}

mod tests {
    #[allow(unused_imports)]
    use crate::ast::{BinaryOp, UnaryOp};
    #[allow(unused_imports)]
    use crate::grammar::ProgramParser;
    #[allow(unused_imports)]
    use crate::ssa::{Block, SSA, optimistic_rewriting};

    #[allow(unused_imports)]
    use super::*;

    #[allow(dead_code)]
    fn placeholder_cost(node: &SSA, costs: &Extraction<SSA>) -> u128 {
        use BinaryOp::*;
        use SSA::*;
        use UnaryOp::*;
        match node {
            Constant(_) => 1,
            Param(_) => 2,
            Phi(_, inputs) => core::cmp::max(costs[&inputs[0]].0, costs[&inputs[1]].0),
            Unary(op, input) => {
                costs[&input].0
                    + match op {
                        Neg => 4,
                        Not => 3,
                    }
            }
            Binary(op, inputs) => {
                costs[&inputs[0]].0
                    + costs[&inputs[1]].0
                    + match op {
                        Add => 5,
                        Sub => 5,
                        Mul => 20,
                        EE => 3,
                        NE => 3,
                        LT => 5,
                        LE => 5,
                        GT => 5,
                        GE => 5,
                    }
            }
            Knot(_) => todo!(),
        }
    }

    #[test]
    fn extract1() {
        let program = r#"
fn test(x) return 2 * x;
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let (dfg, cfg) = optimistic_rewriting(&parsed[0]);
        let costs = extract(&dfg, placeholder_cost);
        let Block::Return(_, id) = cfg[1] else {
            panic!()
        };
        assert_eq!(costs[&id].0, 9);
    }
}
