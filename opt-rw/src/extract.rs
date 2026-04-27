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

pub type DualExtraction<L> = [FxHashMap<Id, (u128, L)>; 2];

pub fn dual_extract<L, A, F1, F2>(egraph: &EGraph<L, A>, cf1: F1, cf2: F2) -> DualExtraction<L>
where
    L: Language,
    A: Analysis<L>,
    F1: Fn(&L, &DualExtraction<L>) -> Option<u128>,
    F2: Fn(&L, &DualExtraction<L>) -> Option<u128>,
{
    let mut costs: DualExtraction<L> = DualExtraction::default();
    let mut priority1: BinaryHeap<QueueElement<L>> = BinaryHeap::new();
    let mut priority2: BinaryHeap<QueueElement<L>> = BinaryHeap::new();
    let mut parents: FxHashMap<Id, Vec<L>> = FxHashMap::default();

    let mut child_dedup: FxHashSet<Id> = FxHashSet::default();
    for class in egraph.classes() {
        for node in class.iter() {
            node.for_each(|child| {
                child_dedup.insert(child);
            });
            for child in child_dedup.drain() {
                parents.entry(child).or_default().push(node.clone());
            }
            if node.is_leaf() {
                priority1.push(QueueElement {
                    node: node.clone(),
                    cost: cf1(&node, &costs).unwrap(),
                });
                priority2.push(QueueElement {
                    node: node.clone(),
                    cost: cf2(&node, &costs).unwrap(),
                });
            }
        }
    }

    while !priority1.is_empty() || !priority2.is_empty() {
        while let Some(QueueElement { node, cost }) = priority1.pop() {
            let id = egraph.lookup(node.clone()).unwrap();
            if costs[0].contains_key(&id) {
                continue;
            }
            costs[0].insert(id, (cost, node));
            for parent in parents.entry(id).or_default() {
                if !costs[0].contains_key(&egraph.lookup(parent.clone()).unwrap())
                    && let Some(cost) = cf1(parent, &costs)
                {
                    priority1.push(QueueElement {
                        node: parent.clone(),
                        cost,
                    });
                }
                if !costs[1].contains_key(&egraph.lookup(parent.clone()).unwrap())
                    && let Some(cost) = cf2(parent, &costs)
                {
                    priority2.push(QueueElement {
                        node: parent.clone(),
                        cost,
                    });
                }
            }
        }

        while let Some(QueueElement { node, cost }) = priority2.pop() {
            let id = egraph.lookup(node.clone()).unwrap();
            if costs[1].contains_key(&id) {
                continue;
            }
            costs[1].insert(id, (cost, node));
            for parent in parents.entry(id).or_default() {
                if !costs[0].contains_key(&egraph.lookup(parent.clone()).unwrap())
                    && let Some(cost) = cf1(parent, &costs)
                {
                    priority1.push(QueueElement {
                        node: parent.clone(),
                        cost,
                    });
                }
                if !costs[1].contains_key(&egraph.lookup(parent.clone()).unwrap())
                    && let Some(cost) = cf2(parent, &costs)
                {
                    priority2.push(QueueElement {
                        node: parent.clone(),
                        cost,
                    });
                }
            }
        }
    }

    costs
}

#[cfg(test)]
mod tests {
    use crate::ast::{BinaryOp, UnaryOp};
    use crate::grammar::ProgramParser;
    use crate::ssa::{Block, SSA, optimistic_rewriting};

    use super::*;

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
            Knot(_) => return None,
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
fn test(x) return ((2 * x) * (2 * x)) * ((2 * x) * (2 * x));
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let (dfg, cfg) = optimistic_rewriting(&parsed[0]);
        let costs = extract(&dfg, placeholder_cost);
        let Block::Return(_, id) = cfg[1] else {
            panic!()
        };
        assert_eq!(costs[&id].0, 96);
    }

    fn cost_a(node: &SSA, costs: &DualExtraction<SSA>) -> Option<u128> {
        placeholder_cost(node, &costs[0])
    }

    fn cost_b(node: &SSA, costs: &DualExtraction<SSA>) -> Option<u128> {
        if let SSA::Binary(BinaryOp::Add, _) = node {
            None
        } else {
            placeholder_cost(node, &costs[0])
        }
    }

    #[test]
    fn dual_extract1() {
        let program = r#"
fn test(x) return 2 * (2 * x);
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let (dfg, cfg) = optimistic_rewriting(&parsed[0]);
        let costs = dual_extract(&dfg, cost_a, cost_b);
        let Block::Return(_, id) = cfg[1] else {
            panic!()
        };
        assert_eq!(costs[0][&id].0, 23);
        assert_eq!(costs[1][&id].0, 30);
    }
}
