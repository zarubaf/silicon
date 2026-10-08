//! Pass 9 (`E010`, the instance graph) and pass 10 (`E008`, the combinational
//! graph). After both passes, each module has its schedule and its
//! dependencies, and the modules are in child-first order.

use super::instances::Linked;
use super::rx::ExModule;
use super::scope::Scope;
use super::structure::Structure;
use super::{error, first_error};
use crate::deps;
use crate::diag::{Diagnostic, ErrorCode, Span};
use crate::scc;
use crate::typed::{Callee, Deps, Design, ModIdx, Module, Node};

/// The modules in an order where each module comes after its children.
pub(super) struct ChildFirst(Vec<ModIdx>);

/// Pass 9: the instance graph has no cycle. An instance lies on a cycle when
/// its parent and its child are in one component.
pub(super) fn instances(scopes: &[Scope], linked: &Linked) -> Result<ChildFirst, Diagnostic> {
    let children: Vec<Vec<usize>> = linked
        .insts
        .iter()
        .map(|insts| {
            insts
                .iter()
                .filter_map(|inst| match inst.callee {
                    Callee::Module(m) => Some(m.index()),
                    Callee::Extern(_) => None,
                })
                .collect()
        })
        .collect();
    let components = scc::components(&children);
    let mut component_of = vec![0; children.len()];
    for (c, component) in components.iter().enumerate() {
        for &m in component {
            component_of[m] = c;
        }
    }
    let mut errors = Vec::new();
    for ((m, scope), insts) in scopes.iter().enumerate().zip(&linked.insts) {
        for (decl, inst) in scope.insts.iter().zip(insts) {
            if let Callee::Module(child) = inst.callee
                && component_of[child.index()] == component_of[m]
            {
                errors.push(error(
                    ErrorCode::E010,
                    decl.span,
                    format!("the instance `{}` is on an instance cycle", decl.name.text),
                ));
            }
        }
    }
    first_error(errors)?;
    Ok(ChildFirst(
        components.into_iter().flatten().map(ModIdx::new).collect(),
    ))
}

/// The source of each node of one module, for the position of an `E008`.
pub(super) struct Sources<'s, 'r> {
    pub scope: &'s Scope<'s>,
    pub rx: &'r ExModule<'r>,
    pub structure: &'s Structure<'r>,
}

impl Sources<'_, '_> {
    fn span(&self, node: Node) -> Span {
        match node {
            Node::Let(l) => self.rx.lets[l.index()].span,
            Node::Output(o) => self.structure.assigns[o.index()].span,
            Node::InstOut(u, _) => self.scope.insts[u.index()].span,
        }
    }
}

/// Pass 10: the combinational graph of each module has no cycle. On success,
/// each module has its schedule and its dependencies, and the modules are in
/// child-first order. `sources` is in the order of `design.modules`.
pub(super) fn combinational(
    design: Design,
    order: &ChildFirst,
    sources: &[Sources],
) -> Result<Design, Diagnostic> {
    let design = child_first(design, order);
    let mut known: Vec<Deps> = Vec::with_capacity(design.modules.len());
    let mut schedules = Vec::with_capacity(design.modules.len());
    let mut errors = Vec::new();
    for (module, old) in design.modules.iter().zip(&order.0) {
        // A child comes first, so its dependencies are known.
        let analysis = deps::analyze(module, |callee| match callee {
            Callee::Module(m) => &known[m.index()],
            Callee::Extern(e) => &design.externs[e.index()].deps,
        });
        match analysis.schedule {
            Ok(schedule) => schedules.push(schedule),
            Err(on_cycle) => {
                let source = &sources[old.index()];
                errors.extend(on_cycle.into_iter().map(|node| {
                    error(
                        ErrorCode::E008,
                        source.span(node),
                        format!("`{}` is on a combinational cycle", name(module, node)),
                    )
                }));
            }
        }
        known.push(analysis.deps);
    }
    first_error(errors)?;
    let modules = design
        .modules
        .into_iter()
        .zip(known)
        .zip(schedules)
        .map(|((module, deps), schedule)| Module {
            schedule,
            deps,
            ..module
        })
        .collect();
    Ok(Design { modules, ..design })
}

/// Reorders the modules and renumbers each reference to a module.
fn child_first(design: Design, order: &ChildFirst) -> Design {
    let mut rank = vec![0; order.0.len()];
    for (new, old) in order.0.iter().enumerate() {
        rank[old.index()] = new;
    }
    let renumber = |m: ModIdx| ModIdx::new(rank[m.index()]);
    let mut ranked: Vec<(usize, Module)> = rank.iter().copied().zip(design.modules).collect();
    ranked.sort_by_key(|(r, _)| *r);
    let modules = ranked
        .into_iter()
        .map(|(_, mut module)| {
            for inst in &mut module.insts {
                if let Callee::Module(m) = inst.callee {
                    inst.callee = Callee::Module(renumber(m));
                }
            }
            module
        })
        .collect();
    Design {
        modules,
        externs: design.externs,
        top: renumber(design.top),
    }
}

fn name(module: &Module, node: Node) -> &str {
    match node {
        Node::Let(l) => &module.lets[l.index()].name,
        Node::Output(o) => &module.outputs[o.index()].name,
        Node::InstOut(u, _) => &module.insts[u.index()].name,
    }
}
