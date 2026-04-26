use core::cmp::Ordering;
use std::collections::BinaryHeap;

use egg::{Analysis, EGraph, Id, Language};
use rustc_hash::{FxHashMap, FxHashSet};

// std::collections::BinaryHeap is a max heap, we want a min heap, so do a custom order.
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
    F: Fn(&L, &Extraction<L>) -> Option<u128>,
{
    let mut costs: Extraction<L> = Extraction::default();
    let mut priority: BinaryHeap<QueueElement<L>> = BinaryHeap::new();
    let mut parents: FxHashMap<Id, Vec<L>> = FxHashMap::default();

    // Initialize data structures:
    // 1. Assemble the "parents" (user nodes) of each e-class ID.
    // 2. Put leaf nodes into priority queue.
    for class in egraph.classes() {
        for node in class.iter() {
            node.for_each(|child| {
                let parents = parents.entry(child).or_default();
                if !parents.contains(node) {
                    parents.push(node.clone());
                }
            });

            // Assuming the cost function is "superior" in Knuth's parlance, starting off by just
            // inserting leaf nodes into the priority queue won't miss out on potentially cheaper
            // extraction candidates.
            if node.is_leaf() {
                priority.push(QueueElement {
                    node: node.clone(),
                    cost: cf(&node, &costs).unwrap(),
                });
            }
        }
    }

    while let Some(QueueElement { node, cost }) = priority.pop() {
        let id = egraph.lookup(node.clone()).unwrap();
        // Due to the Dijkstra style extraction, if we've found an extraction of an e-class, it is
        // already the best.
        if costs.contains_key(&id) {
            continue;
        }

        // Once an e-class has a cost, that cost won't get better later. Transitively, the cost of
        // nodes also won't change once its children e-classes have been extracted.
        assert_eq!(cost, cf(&node, &costs).unwrap());
        costs.insert(id, (cost, node));
        for parent in parents.entry(id).or_default() {
            // A parent of an e-class may be in an e-class we've already extracted.
            if costs.contains_key(&egraph.lookup(parent.clone()).unwrap()) {
                continue;
            }

            // Once a parent node's cost can be calculated (its children e-classes have all been)
            // assigned costs, then it can be added to the queue.
            if let Some(cost) = cf(parent, &costs) {
                priority.push(QueueElement {
                    node: parent.clone(),
                    cost,
                });
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
    fn placeholder_cost(node: &SSA, costs: &Extraction<SSA>) -> Option<u128> {
        use BinaryOp::*;
        use SSA::*;
        use UnaryOp::*;
        Some(match node {
            Constant(_) => 1,
            Param(_) => 2,
            Phi(_, inputs) => core::cmp::max(costs.get(&inputs[0])?.0, costs.get(&inputs[1])?.0),
            Unary(op, input) => {
                costs.get(&input)?.0
                    + match op {
                        Neg => 4,
                        Not => 3,
                    }
            }
            Binary(op, inputs) => {
                costs.get(&inputs[0])?.0
                    + costs.get(&inputs[1])?.0
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
        })
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

    #[test]
    fn extract2() {
        let program = r#"
fn test(x) return ((2 * x) - (2 * x)) * ((2 * x) - (2 * x));
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let (dfg, cfg) = optimistic_rewriting(&parsed[0]);
        let costs = extract(&dfg, placeholder_cost);
        let Block::Return(_, id) = cfg[1] else {
            panic!()
        };
        assert_eq!(costs[&id].0, 66);
    }
}
