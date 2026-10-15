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

/// [`analyze`] and its work, so that a test can bound the cost without a clock.
/// The work counts one step for each node and each edge of the graph, for each
/// expression the graph build walks, for each step of the search for the
/// inputs, and for each element of the schedule and of the result. It counts
/// the nodes that no output reaches too. The component search counts as its
/// nodes and edges, since `scc::components` is linear.
fn analyze_counted<'d>(
    module: &Module,
    child_deps: impl Fn(Callee) -> &'d Deps,
) -> (Analysis, usize) {
    let graph = Graph::build(module, &child_deps);
    let mut work = graph.work + graph.nodes.len();
    work += graph.reads.iter().map(Vec::len).sum::<usize>();
    work += graph.inputs.iter().map(Vec::len).sum::<usize>();
    let components = scc::components(&graph.reads);
    let outputs: Vec<usize> =
        (graph.output_base..graph.output_base + module.outputs.len()).collect();
    let (reached, reach_work) = reached_inputs(&graph, &outputs, module.inputs.len());
    work += reach_work;
    let deps: Deps = reached
        .into_iter()
        .map(|inputs| inputs.into_iter().map(InputIdx::new).collect())
        .collect();
    work += deps.iter().map(Vec::len).sum::<usize>() + deps.len();
    let on_cycle: Vec<Node> = components
        .iter()
        .filter(|component| {
            work += component.len() + graph.reads[component[0]].len();
            scc::is_cycle(component, &graph.reads)
        })
        .flatten()
        .map(|&v| graph.nodes[v])
        .collect();
    work += graph.nodes.len();
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

/// The inputs that each output node reaches, as sorted input positions, and the
/// work of the search. A cycle changes nothing: a node reaches what its
/// reads reach. With `outputs` at most `input_count`, one search runs from
/// each output, and a stamp per node marks the visited nodes. Otherwise one
/// search runs from each input over the reversed edges. Both cost
/// `O(E * min(inputs, outputs))` for `E` edges. The result can be that large.
fn reached_inputs(
    graph: &Graph,
    outputs: &[usize],
    input_count: usize,
) -> (Vec<Vec<usize>>, usize) {
    if outputs.len() <= input_count {
        reached_by_output(graph, outputs, input_count)
    } else {
        reached_by_input(graph, outputs, input_count)
    }
}

fn reached_by_output(
    graph: &Graph,
    outputs: &[usize],
    input_count: usize,
) -> (Vec<Vec<usize>>, usize) {
    let mut work = 0;
    let mut visited = vec![usize::MAX; graph.nodes.len()];
    let mut input_seen = vec![usize::MAX; input_count];
    let mut sets = Vec::with_capacity(outputs.len());
    for (o, &start) in outputs.iter().enumerate() {
        let mut found = Vec::new();
        let mut pending = vec![start];
        visited[start] = o;
        while let Some(v) = pending.pop() {
            work += 1 + graph.inputs[v].len() + graph.reads[v].len();
            for i in &graph.inputs[v] {
                if input_seen[i.index()] != o {
                    input_seen[i.index()] = o;
                    found.push(i.index());
                }
            }
            for &w in &graph.reads[v] {
                if visited[w] != o {
                    visited[w] = o;
                    pending.push(w);
                }
            }
        }
        work += found.len();
        found.sort_unstable();
        sets.push(found);
    }
    (sets, work)
}

fn reached_by_input(
    graph: &Graph,
    outputs: &[usize],
    input_count: usize,
) -> (Vec<Vec<usize>>, usize) {
    let mut work = graph.nodes.len();
    let mut readers: Vec<Vec<usize>> = vec![Vec::new(); graph.nodes.len()];
    let mut seeds: Vec<Vec<usize>> = vec![Vec::new(); input_count];
    for v in 0..graph.nodes.len() {
        work += graph.reads[v].len() + graph.inputs[v].len();
        for &w in &graph.reads[v] {
            readers[w].push(v);
        }
        for i in &graph.inputs[v] {
            seeds[i.index()].push(v);
        }
    }
    let mut output_of = vec![None; graph.nodes.len()];
    for (o, &v) in outputs.iter().enumerate() {
        output_of[v] = Some(o);
    }
    let mut sets: Vec<Vec<usize>> = vec![Vec::new(); outputs.len()];
    let mut visited = vec![usize::MAX; graph.nodes.len()];
    for (i, seed) in seeds.iter().enumerate() {
        let mut pending = Vec::new();
        for &v in seed {
            if visited[v] != i {
                visited[v] = i;
                pending.push(v);
            }
        }
        while let Some(v) = pending.pop() {
            work += 1 + readers[v].len();
            if let Some(o) = output_of[v] {
                sets[o].push(i);
            }
            for &u in &readers[v] {
                if visited[u] != i {
                    visited[u] = i;
                    pending.push(u);
                }
            }
        }
    }
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
    /// The expressions that the build walked.
    work: usize,
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
            work: 0,
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
        self.work += 1;
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

    /// The inputs that `expr` reaches by walking the lets and the outputs, with
    /// a set of visited names so that a cycle ends.
    fn naive(
        module: &Module,
        expr: &Expr,
        found: &mut std::collections::BTreeSet<usize>,
        seen: &mut std::collections::BTreeSet<(bool, usize)>,
    ) {
        match expr {
            Expr::Input(i) => {
                found.insert(i.index());
            }
            Expr::Let(l) => {
                if seen.insert((false, l.index())) {
                    naive(module, &module.lets[l.index()].expr, found, seen);
                }
            }
            Expr::Output(o) => {
                if seen.insert((true, o.index())) {
                    naive(module, &module.assigns[o.index()], found, seen);
                }
            }
            Expr::Bin(_, a, b) => {
                naive(module, a, found, seen);
                naive(module, b, found, seen);
            }
            _ => {}
        }
    }

    #[test]
    fn shared_and_cyclic_lets_give_the_dependencies_of_a_walk_with_no_sharing() {
        let mut seed = 0x2545_f491_4f6c_dd1du64;
        let mut next = move |bound: usize| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            usize::try_from(seed % u64::try_from(bound).unwrap_or(1)).unwrap_or(0)
        };
        for round in 0..200 {
            // Few inputs with many outputs, and the reverse, take both searches.
            let (inputs, lets, outputs) = if round % 2 == 0 {
                (6, 40, 3)
            } else {
                (2, 30, 7)
            };
            let names: Vec<String> = (0..inputs).map(|i| format!("i{i}")).collect();
            let names: Vec<&str> = names.iter().map(String::as_str).collect();
            let out_names: Vec<String> = (0..outputs).map(|i| format!("o{i}")).collect();
            let out_names: Vec<&str> = out_names.iter().map(String::as_str).collect();
            // A let reads any let, also a later one, so the graph has cycles. A
            // read of an output makes the outputs read each other.
            let operand = |next: &mut dyn FnMut(usize) -> usize| match next(4) {
                0 | 1 => Expr::Let(LetIdx::new(next(lets))),
                2 => Expr::Output(OutputIdx::new(next(outputs))),
                _ => input(next(inputs)),
            };
            let exprs: Vec<Expr> = (0..lets)
                .map(|_| bin(operand(&mut next), operand(&mut next)))
                .collect();
            let assigns: Vec<Expr> = (0..outputs).map(|_| operand(&mut next)).collect();
            let m = with_lets(module(&names, &out_names, vec![], assigns), exprs);
            let want: Deps = m
                .assigns
                .iter()
                .map(|assign| {
                    let mut found = std::collections::BTreeSet::new();
                    naive(
                        &m,
                        assign,
                        &mut found,
                        &mut std::collections::BTreeSet::new(),
                    );
                    found.into_iter().map(InputIdx::new).collect()
                })
                .collect();
            assert_eq!(infer(&m, |_| unreachable!("no instance")), want);
        }
    }

    /// `out` reads the last let. `k` lets of each shape, built by `lets`.
    fn one_output(inputs: usize, lets: Vec<Expr>) -> Module {
        let names: Vec<String> = (0..inputs).map(|i| format!("i{i}")).collect();
        let names: Vec<&str> = names.iter().map(String::as_str).collect();
        let last = Expr::Let(LetIdx::new(lets.len() - 1));
        with_lets(module(&names, &["y"], vec![], vec![last]), lets)
    }

    fn l(i: usize) -> Expr {
        Expr::Let(LetIdx::new(i))
    }

    fn assert_in_proportion(shape: impl Fn(usize) -> Module) {
        let (small, large) = (work(&shape(400)), work(&shape(800)));
        assert!(large * 100 <= small * 220, "{small} then {large}");
    }

    #[test]
    fn the_work_of_serial_diamonds_stays_in_proportion() {
        // s0 = i0; a_k = s(k-1) & ik; b_k = s(k-1); s_k = a_k & b_k.
        assert_in_proportion(|n| {
            let mut lets = vec![input(0)];
            for k in 1..=n {
                let s = lets.len() - 1;
                lets.push(bin(l(s), input(k)));
                lets.push(l(s));
                lets.push(bin(l(s + 1), l(s + 2)));
            }
            one_output(n + 1, lets)
        });
    }

    #[test]
    fn the_work_of_a_ladder_stays_in_proportion() {
        // lk = l(k-1) & ik; mk = m(k-1) & lk, with m0 = l0.
        assert_in_proportion(|n| {
            let mut lets = vec![input(0), l(0)];
            for k in 1..n {
                let (prev_l, prev_m) = (lets.len() - 2, lets.len() - 1);
                lets.push(bin(l(prev_l), input(k)));
                lets.push(bin(l(prev_m), l(prev_l + 2)));
            }
            one_output(n, lets)
        });
    }

    #[test]
    fn the_work_of_many_outputs_with_few_inputs_stays_in_proportion() {
        // n outputs read the lets of one chain, which reads two inputs.
        let shape = |n: usize| {
            let lets: Vec<Expr> = (0..n)
                .map(|k| match k {
                    0 => input(0),
                    _ => bin(l(k - 1), input(1)),
                })
                .collect();
            let assigns: Vec<Expr> = (0..n).map(l).collect();
            let names: Vec<String> = (0..n).map(|i| format!("o{i}")).collect();
            let names: Vec<&str> = names.iter().map(String::as_str).collect();
            with_lets(module(&["a", "b"], &names, vec![], assigns), lets)
        };
        let (small, large) = (work(&shape(1_000)), work(&shape(2_000)));
        assert!(large * 100 <= small * 220, "{small} then {large}");
    }
}
