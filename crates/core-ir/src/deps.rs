// SPDX-License-Identifier: Apache-2.0
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
    analyze_counted(module, child_deps).0
}

/// [`analyze`] and the number of steps of its search for the inputs. The count
/// is the work of the analysis, so that a test can bound the cost without a clock.
fn analyze_counted<'d>(
    module: &Module,
    child_deps: impl Fn(Callee) -> &'d Deps,
) -> (Analysis, usize) {
    let graph = Graph::build(module, &child_deps);
    let components = scc::components(&graph.reads);
    let mut component_of = vec![0; graph.nodes.len()];
    for (c, component) in components.iter().enumerate() {
        for &v in component {
            component_of[v] = c;
        }
    }
    let outputs: Vec<usize> = (0..module.outputs.len())
        .map(|o| component_of[graph.output_base + o])
        .collect();
    let (reached, work) = reached_inputs(&graph, &components, &component_of, &outputs);
    let deps = reached
        .into_iter()
        .map(|inputs| inputs.into_iter().map(InputIdx::new).collect())
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
    (Analysis { deps, schedule }, work)
}

/// The inputs that each of the `outputs` components reaches, as sorted input
/// positions, and the work of the search. A component comes after each
/// component that it reads.
///
/// Only the components that an output reaches take part. A set of inputs is
/// stored for an output component and for a component that two components
/// read. A component with a single reader adds its inputs to the set of that
/// reader, so a chain of such components costs one pass and no set of its own.
fn reached_inputs(
    graph: &Graph,
    components: &[Vec<usize>],
    component_of: &[usize],
    outputs: &[usize],
) -> (Vec<Vec<usize>>, usize) {
    let mut work = 0;
    let mut stored = vec![false; components.len()];
    let mut wanted = vec![false; components.len()];
    for &c in outputs {
        stored[c] = true;
        wanted[c] = true;
    }
    // A reader comes after what it reads, so the backward pass sees every
    // reader of a component before the component.
    let mut readers = vec![0usize; components.len()];
    let mut last_reader = vec![usize::MAX; components.len()];
    for (c, component) in components.iter().enumerate().rev() {
        if !wanted[c] {
            continue;
        }
        for &v in component {
            work += 1;
            for &w in &graph.reads[v] {
                work += 1;
                let read = component_of[w];
                if read != c {
                    wanted[read] = true;
                    if last_reader[read] != c {
                        last_reader[read] = c;
                        readers[read] += 1;
                    }
                }
            }
        }
    }
    for (c, &count) in readers.iter().enumerate() {
        stored[c] |= count > 1;
    }
    let mut reached: Vec<Vec<usize>> = vec![Vec::new(); components.len()];
    // The last component that took the set of a stored component, and whether
    // a component with one reader was taken: each is taken once.
    let mut taken_by = vec![usize::MAX; components.len()];
    let mut taken = vec![false; components.len()];
    for c in (0..components.len()).filter(|&c| stored[c]) {
        let mut inputs = Vec::new();
        let mut pending = vec![c];
        while let Some(x) = pending.pop() {
            for &v in &components[x] {
                work += 1 + graph.inputs[v].len();
                inputs.extend(graph.inputs[v].iter().map(|i| i.index()));
                for &w in &graph.reads[v] {
                    work += 1;
                    let read = component_of[w];
                    if read == x {
                        continue;
                    }
                    if stored[read] {
                        if taken_by[read] != c {
                            taken_by[read] = c;
                            work += reached[read].len();
                            inputs.extend_from_slice(&reached[read]);
                        }
                    } else if !taken[read] {
                        taken[read] = true;
                        pending.push(read);
                    }
                }
            }
        }
        work += inputs.len();
        inputs.sort_unstable();
        inputs.dedup();
        reached[c] = inputs;
    }
    let sets = outputs.iter().map(|&c| reached[c].clone()).collect();
    (sets, work)
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

    fn port(name: &str, position: usize) -> Port {
        Port {
            name: name.into(),
            width: std::num::NonZeroU32::MIN,
            position,
        }
    }

    fn module(inputs: &[&str], outputs: &[&str], insts: Vec<Inst>, assigns: Vec<Expr>) -> Module {
        Module {
            name: "m".into(),
            inputs: inputs.iter().enumerate().map(|(i, n)| port(n, i)).collect(),
            outputs: outputs
                .iter()
                .enumerate()
                .map(|(i, n)| port(n, inputs.len() + i))
                .collect(),
            clock: None,
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

    fn bin(a: Expr, b: Expr) -> Expr {
        Expr::Bin(BinOp::And, Box::new(a), Box::new(b))
    }

    fn input(i: usize) -> Expr {
        Expr::Input(InputIdx::new(i))
    }

    fn with_lets(mut m: Module, exprs: Vec<Expr>) -> Module {
        m.lets = exprs
            .into_iter()
            .enumerate()
            .map(|(i, expr)| crate::typed::Let {
                name: format!("l{i}"),
                width: std::num::NonZeroU32::MIN,
                expr,
            })
            .collect();
        m
    }

    /// The chain `l0 = i0`, `lk = l(k-1) & ik`, read by one output.
    fn chain(n: usize) -> Module {
        let names: Vec<String> = (0..n).map(|i| format!("i{i}")).collect();
        let names: Vec<&str> = names.iter().map(String::as_str).collect();
        let lets = (0..n)
            .map(|k| match k {
                0 => input(0),
                _ => bin(Expr::Let(LetIdx::new(k - 1)), input(k)),
            })
            .collect();
        let last = Expr::Let(LetIdx::new(n - 1));
        with_lets(module(&names, &["y"], vec![], vec![last]), lets)
    }

    fn work(module: &Module) -> usize {
        analyze_counted(module, |_| unreachable!("the module has no instance")).1
    }

    #[test]
    fn the_work_of_a_chain_grows_in_proportion_to_its_length() {
        let (small, large) = (work(&chain(2_000)), work(&chain(4_000)));
        // Twice the statements: at most about twice the work.
        assert!(large * 100 <= small * 220, "{small} then {large}");
    }

    #[test]
    fn the_work_of_a_let_read_twice_by_one_reader_stays_in_proportion() {
        // Each let reads the one before it twice, so a walk that follows each
        // edge doubles at each step.
        let doubled = |n: usize| {
            let names: Vec<String> = (0..n).map(|i| format!("i{i}")).collect();
            let names: Vec<&str> = names.iter().map(String::as_str).collect();
            let lets = (0..n)
                .map(|k| match k {
                    0 => input(0),
                    _ => bin(Expr::Let(LetIdx::new(k - 1)), Expr::Let(LetIdx::new(k - 1))),
                })
                .collect();
            let last = Expr::Let(LetIdx::new(n - 1));
            with_lets(module(&names, &["y"], vec![], vec![last]), lets)
        };
        let (small, large) = (work(&doubled(2_000)), work(&doubled(4_000)));
        assert!(large * 100 <= small * 220, "{small} then {large}");
    }

    /// The inputs that `expr` reaches by walking the lets, with no sharing.
    fn naive(module: &Module, expr: &Expr, found: &mut std::collections::BTreeSet<usize>) {
        match expr {
            Expr::Input(i) => {
                found.insert(i.index());
            }
            Expr::Let(l) => naive(module, &module.lets[l.index()].expr, found),
            Expr::Bin(_, a, b) => {
                naive(module, a, found);
                naive(module, b, found);
            }
            _ => {}
        }
    }

    #[test]
    fn shared_lets_give_the_dependencies_of_a_walk_with_no_sharing() {
        let mut seed = 0x2545_f491_4f6c_dd1du64;
        let mut next = move |bound: usize| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            usize::try_from(seed % u64::try_from(bound).unwrap_or(1)).unwrap_or(0)
        };
        for _ in 0..50 {
            let (inputs, lets) = (6, 40);
            let names: Vec<String> = (0..inputs).map(|i| format!("i{i}")).collect();
            let names: Vec<&str> = names.iter().map(String::as_str).collect();
            let operand = |k: usize, next: &mut dyn FnMut(usize) -> usize| match next(3) {
                0 | 1 if k > 0 => Expr::Let(LetIdx::new(next(k))),
                _ => input(next(inputs)),
            };
            let exprs: Vec<Expr> = (0..lets)
                .map(|k| bin(operand(k, &mut next), operand(k, &mut next)))
                .collect();
            let assigns: Vec<Expr> = (0..4).map(|_| Expr::Let(LetIdx::new(next(lets)))).collect();
            let m = with_lets(
                module(&names, &["a", "b", "c", "d"], vec![], assigns),
                exprs,
            );
            let want: Deps = m
                .assigns
                .iter()
                .map(|assign| {
                    let mut found = std::collections::BTreeSet::new();
                    naive(&m, assign, &mut found);
                    found.into_iter().map(InputIdx::new).collect()
                })
                .collect();
            assert_eq!(infer(&m, |_| unreachable!("no instance")), want);
        }
    }
}
