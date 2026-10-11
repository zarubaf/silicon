// SPDX-License-Identifier: Apache-2.0
//! What the expressions of a generated module can read, and the
//! combinational graph that the generator keeps acyclic.

use std::collections::BTreeSet;

use crate::ast::Expr;

/// Where a value comes from, for the combinational graph.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Source {
    /// The data input at this position among the data inputs.
    Input(usize),
    /// A register. A read of it makes no edge.
    State,
    /// A node of the graph: a `let`, an output, or an instance output.
    Node(usize),
}

/// A value that an expression can read.
#[derive(Clone)]
pub(super) struct Value {
    /// A name or a `NAME.PORT`.
    pub expr: Expr,
    pub width: u32,
    pub source: Source,
}

#[derive(Clone)]
pub(super) struct Mem {
    pub name: String,
    pub width: u32,
    pub depth: u32,
}

#[derive(Clone, Default)]
pub(super) struct Scope {
    pub values: Vec<Value>,
    pub mems: Vec<Mem>,
}

impl Scope {
    /// The sources of the values that `expr` reads. The words of a memory
    /// are no source, so a read gives only the sources of its address.
    pub fn sources(&self, expr: &Expr) -> Vec<Source> {
        match expr {
            Expr::Ref(_) | Expr::InstOut { .. } => self
                .values
                .iter()
                .filter(|v| v.expr == *expr)
                .map(|v| v.source)
                .collect(),
            Expr::Const { .. } => Vec::new(),
            Expr::Unary { arg, .. }
            | Expr::Extract { arg, .. }
            | Expr::Replicate { arg, .. }
            | Expr::Read { addr: arg, .. } => self.sources(arg),
            Expr::Binary { lhs, rhs, .. } | Expr::Icmp { lhs, rhs, .. } => {
                let mut out = self.sources(lhs);
                out.extend(self.sources(rhs));
                out
            }
            Expr::Mux {
                cond, then, els, ..
            } => {
                let mut out = self.sources(cond);
                out.extend(self.sources(then));
                out.extend(self.sources(els));
                out
            }
        }
    }

    /// The values and memories of the scope without the values that depend
    /// on one of `nodes` in `graph`.
    pub fn without(&self, graph: &Graph, nodes: &BTreeSet<usize>) -> Scope {
        let values = self
            .values
            .iter()
            .filter(|v| graph.support(&[v.source]).nodes.is_disjoint(nodes))
            .cloned()
            .collect();
        Scope {
            values,
            mems: self.mems.clone(),
        }
    }
}

/// What a set of sources reads combinationally, directly or through nodes.
pub(super) struct Support {
    /// The data input positions.
    pub inputs: BTreeSet<usize>,
    /// The nodes, the start nodes included.
    pub nodes: BTreeSet<usize>,
}

/// The combinational graph of a module: the direct reads of each node.
#[derive(Default)]
pub(super) struct Graph {
    reads: Vec<Vec<Source>>,
}

impl Graph {
    /// A new node that reads nothing yet.
    pub fn node(&mut self) -> usize {
        self.reads.push(Vec::new());
        self.reads.len() - 1
    }

    /// Records that `node` reads `sources`.
    pub fn read(&mut self, node: usize, sources: &[Source]) {
        if let Some(reads) = self.reads.get_mut(node) {
            reads.extend_from_slice(sources);
        }
    }

    pub fn support(&self, sources: &[Source]) -> Support {
        let mut support = Support {
            inputs: BTreeSet::new(),
            nodes: BTreeSet::new(),
        };
        let mut work = sources.to_vec();
        while let Some(source) = work.pop() {
            match source {
                Source::Input(i) => {
                    support.inputs.insert(i);
                }
                Source::State => {}
                Source::Node(n) => {
                    if support.nodes.insert(n) {
                        work.extend(self.reads.get(n).into_iter().flatten());
                    }
                }
            }
        }
        support
    }
}
