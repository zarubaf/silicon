// SPDX-License-Identifier: Apache-2.0
//! The strongly connected components of a directed graph, by Tarjan's
//! algorithm. The search keeps its own stack, so a deep graph cannot overflow
//! the call stack, and it takes linear time.

/// The components of the graph whose node `v` has the successors `succ[v]`.
/// Each successor is a node of the graph. A component comes after every
/// component that it reaches. With an edge from each reader to what it reads,
/// the components are thus in evaluation order.
pub(crate) fn components(succ: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let mut search = Search {
        index: vec![None; succ.len()],
        low: vec![0; succ.len()],
        on_stack: vec![false; succ.len()],
        stack: Vec::new(),
        open: Vec::new(),
        next: 0,
    };
    let mut found = Vec::new();
    for root in 0..succ.len() {
        if search.index[root].is_none() {
            search.enter(root);
            search.run(succ, &mut found);
        }
    }
    found
}

struct Search {
    /// The visit number of each node, once the search enters it.
    index: Vec<Option<usize>>,
    /// The lowest visit number that each node reaches on the stack.
    low: Vec<usize>,
    on_stack: Vec<bool>,
    stack: Vec<usize>,
    /// The open nodes of the search, each with the position of its next edge.
    open: Vec<(usize, usize)>,
    next: usize,
}

impl Search {
    fn enter(&mut self, v: usize) {
        self.index[v] = Some(self.next);
        self.low[v] = self.next;
        self.next += 1;
        self.stack.push(v);
        self.on_stack[v] = true;
        self.open.push((v, 0));
    }

    fn run(&mut self, succ: &[Vec<usize>], found: &mut Vec<Vec<usize>>) {
        while let Some((v, edge)) = self.open.pop() {
            if let Some(&w) = succ[v].get(edge) {
                self.open.push((v, edge + 1));
                match self.index[w] {
                    None => self.enter(w),
                    Some(iw) if self.on_stack[w] => self.low[v] = self.low[v].min(iw),
                    Some(_) => {}
                }
                continue;
            }
            if let Some(&(parent, _)) = self.open.last() {
                self.low[parent] = self.low[parent].min(self.low[v]);
            }
            if self.index[v] == Some(self.low[v]) {
                let mut component = Vec::new();
                while let Some(w) = self.stack.pop() {
                    self.on_stack[w] = false;
                    component.push(w);
                    if w == v {
                        break;
                    }
                }
                found.push(component);
            }
        }
    }
}

/// Whether the component lies on a cycle: it has two nodes or a self edge.
pub(crate) fn is_cycle(component: &[usize], succ: &[Vec<usize>]) -> bool {
    match component {
        [v] => succ[*v].contains(v),
        _ => true,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn components_come_after_what_they_reach() {
        // 0 -> 1 -> 2 -> 1, 3 -> 3
        let succ = vec![vec![1], vec![2], vec![1], vec![3]];
        let found = components(&succ);
        assert_eq!(found.len(), 3);
        assert_eq!(found[0].len(), 2);
        assert_eq!(found[1], [0]);
        assert_eq!(found[2], [3]);
        assert!(is_cycle(&found[0], &succ));
        assert!(!is_cycle(&found[1], &succ));
        assert!(is_cycle(&found[2], &succ));
    }

    #[test]
    fn a_long_chain_does_not_overflow() {
        let succ: Vec<Vec<usize>> = (0..1_000_000)
            .map(|v| vec![v + 1])
            .chain([vec![]])
            .collect();
        let found = components(&succ);
        assert_eq!(found.len(), 1_000_001);
        assert_eq!(found[0], [1_000_000]);
    }
}
