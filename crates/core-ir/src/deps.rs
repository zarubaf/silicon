//! The port dependencies and the combinational graph of a module (spec
//! section 5.3).
//!
//! The graph has one node for each `let`, each output, and each instance
//! output. A node reads the nodes and the inputs that its expression names:
//! a read of an output of the module reads the node of that output.
//! A register read and the stored contents of a memory make no edge, and an
//! instance output reads only the connections of the inputs in its
//! dependencies. The inference is syntactic reachability with no
//! simplification.

use crate::scc;
use crate::typed::{Callee, Deps, Expr, InputIdx, InstIdx, LetIdx, Module, Node, OutputIdx};

/// The inputs that each output of `module` reads in the same cycle.
/// `child_deps` gives the dependencies of each module or extern that `module`
/// instantiates. A cycle in the graph does not change the result: an output
/// depends on each input that it reaches.
///
/// # Panics
/// The module and the child dependencies must come from [`crate::check::check`].
/// An index that is out of range in an inconsistent module panics.
pub fn infer<'d>(module: &Module, child_deps: impl Fn(Callee) -> &'d Deps) -> Deps {
    analyze(module, child_deps).deps
}

/// The result of the analysis of one module.
pub(crate) struct Analysis {
    pub deps: Deps,
    /// The nodes in evaluation order, or the nodes that lie on a cycle.
    pub schedule: Result<Vec<Node>, Vec<Node>>,
}

/// Infers the dependencies and orders the graph of `module`.
pub(crate) fn analyze<'d>(module: &Module, child_deps: impl Fn(Callee) -> &'d Deps) -> Analysis {
    let graph = Graph::build(module, &child_deps);
    let components = scc::components(&graph.reads);
    let mut component_of = vec![0; graph.nodes.len()];
    for (c, component) in components.iter().enumerate() {
        for &v in component {
            component_of[v] = c;
        }
    }
    // The inputs that each component reaches, as sorted input positions. A
    // component comes after each component that it reads.
    let mut reached: Vec<Vec<usize>> = Vec::with_capacity(components.len());
    for (c, component) in components.iter().enumerate() {
        let mut inputs = Vec::new();
        for &v in component {
            inputs.extend(graph.inputs[v].iter().map(|i| i.index()));
            for &w in &graph.reads[v] {
                if component_of[w] != c {
                    inputs.extend_from_slice(&reached[component_of[w]]);
                }
            }
        }
        inputs.sort_unstable();
        inputs.dedup();
        reached.push(inputs);
    }
    let deps = (0..module.outputs.len())
        .map(|o| {
            reached[component_of[graph.output_base + o]]
                .iter()
                .map(|&i| InputIdx::new(i))
                .collect()
        })
        .collect();
    let on_cycle: Vec<Node> = components
        .iter()
        .filter(|component| scc::is_cycle(component, &graph.reads))
        .flatten()
        .map(|&v| graph.nodes[v])
        .collect();
    let schedule = if on_cycle.is_empty() {
        Ok(components
            .iter()
            .flatten()
            .map(|&v| graph.nodes[v])
            .collect())
    } else {
        Err(on_cycle)
    };
    Analysis { deps, schedule }
}

/// The combinational graph. A node is a position in `nodes`: the `let`s
/// first, then the outputs, then the outputs of each instance.
struct Graph {
    nodes: Vec<Node>,
    /// For each node, the nodes that it reads.
    reads: Vec<Vec<usize>>,
    /// For each node, the inputs that it reads directly.
    inputs: Vec<Vec<InputIdx>>,
    output_base: usize,
}

impl Graph {
    fn build<'d>(module: &Module, child_deps: &impl Fn(Callee) -> &'d Deps) -> Graph {
        let mut nodes: Vec<Node> = (0..module.lets.len())
            .map(|l| Node::Let(LetIdx::new(l)))
            .collect();
        let output_base = nodes.len();
        nodes.extend((0..module.outputs.len()).map(|o| Node::Output(OutputIdx::new(o))));
        let mut inst_base = Vec::with_capacity(module.insts.len());
        for (u, inst) in module.insts.iter().enumerate() {
            inst_base.push(nodes.len());
            let outputs = child_deps(inst.callee).len();
            nodes.extend((0..outputs).map(|q| Node::InstOut(InstIdx::new(u), OutputIdx::new(q))));
        }
        let mut graph = Graph {
            reads: vec![Vec::new(); nodes.len()],
            inputs: vec![Vec::new(); nodes.len()],
            nodes,
            output_base,
        };
        let mut v = 0;
        for l in &module.lets {
            graph.read(v, &l.expr, &inst_base);
            v += 1;
        }
        for assign in &module.assigns {
            graph.read(v, assign, &inst_base);
            v += 1;
        }
        for inst in &module.insts {
            for inputs in child_deps(inst.callee) {
                for i in inputs {
                    graph.read(v, &inst.inputs[i.index()], &inst_base);
                }
                v += 1;
            }
        }
        graph
    }

    /// Adds the reads of `expr` to node `v`.
    fn read(&mut self, v: usize, expr: &Expr, inst_base: &[usize]) {
        match expr {
            Expr::Input(i) => self.inputs[v].push(*i),
            Expr::Let(l) => self.reads[v].push(l.index()),
            Expr::Output(o) => self.reads[v].push(self.output_base + o.index()),
            Expr::InstOut(u, q) => self.reads[v].push(inst_base[u.index()] + q.index()),
            Expr::Reg(_) | Expr::Const(_) => {}
            // The address makes edges; the stored contents make none.
            Expr::Read(_, arg)
            | Expr::Un(_, arg)
            | Expr::Extract(arg, ..)
            | Expr::Replicate(arg, _) => self.read(v, arg, inst_base),
            Expr::Bin(_, a, b) | Expr::Icmp(_, a, b) => {
                self.read(v, a, inst_base);
                self.read(v, b, inst_base);
            }
            Expr::Mux(c, t, e) => {
                self.read(v, c, inst_base);
                self.read(v, t, inst_base);
                self.read(v, e, inst_base);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::BinOp;
    use crate::typed::{Inst, Port};

    fn port(name: &str) -> Port {
        Port {
            name: name.into(),
            width: std::num::NonZeroU32::MIN,
        }
    }

    fn module(inputs: &[&str], outputs: &[&str], insts: Vec<Inst>, assigns: Vec<Expr>) -> Module {
        Module {
            name: "m".into(),
            inputs: inputs.iter().map(|n| port(n)).collect(),
            outputs: outputs.iter().map(|n| port(n)).collect(),
            has_clock: false,
            lets: vec![],
            regs: vec![],
            mems: vec![],
            insts,
            assigns,
            schedule: vec![],
            deps: Deps::default(),
        }
    }

    #[test]
    fn an_output_through_a_child_gets_the_child_dependencies() {
        // The child output 0 reads its input 1, and output 1 reads nothing.
        let child: Deps = vec![vec![InputIdx::new(1)], vec![]];
        let inst = Inst {
            name: "u".into(),
            callee: Callee::Extern(crate::typed::ExternIdx::new(0)),
            inputs: vec![Expr::Input(InputIdx::new(0)), Expr::Input(InputIdx::new(2))],
        };
        let out = |q| Expr::InstOut(InstIdx::new(0), OutputIdx::new(q));
        let parent = module(
            &["a", "b", "c"],
            &["x", "y", "z"],
            vec![inst],
            vec![
                out(0),
                out(1),
                Expr::Bin(
                    BinOp::And,
                    Box::new(out(1)),
                    Box::new(Expr::Input(InputIdx::new(1))),
                ),
            ],
        );
        let deps = infer(&parent, |_| &child);
        assert_eq!(
            deps,
            vec![vec![InputIdx::new(2)], vec![], vec![InputIdx::new(1)]]
        );
    }
}
