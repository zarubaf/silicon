// SPDX-License-Identifier: Apache-2.0
//! The description of an instantiation (`Body`, `Iface`, `Inst`) and the `Design` of an
//! elaboration. They are the data that the instantiation fills and the lowering reads.

use super::public::{PubKey, Public};
use crate::agg::Agg;
use crate::eval::Let;
use crate::hw::{Graph, Kind, Port, PortId};
#[cfg(test)]
use crate::names::encode;
use crate::names::{Name, PathId, Paths, Sym};
use crate::types::{Ty, TyId, Types};
use crate::value::Value;
use parse::StackError;
use parse::ast::Pos;
use std::collections::{BTreeMap, BTreeSet};

/// A port declaration. A port keeps its source name. A family entry has its key.
pub(crate) struct PortDecl {
    pub sym: Sym,
    pub key: Option<u32>,
    pub input: bool,
    pub ty: Ty,
    pub tid: TyId,
    pub pos: Pos,
}

pub(crate) struct RegDecl {
    pub path: PathId,
    pub ty: Ty,
    pub init: Value,
    pub pos: Pos,
}

/// A position with the number of the call frame that ran it (`Ev::call`).
pub(crate) type Here = (Pos, usize);

/// A memory of one instantiation (section 7.6): its name, its path, its word type, its depth,
/// and its `mem` statement. `read` holds the request of its first `read_port` call: the address
/// and the enable. `write` holds the request of its first `write_port` call: the address, the
/// data, and the enable. Each part of a request is after its typed use. `read_at` and `write_at`
/// hold the positions of the first calls, each with its call frame number (section 6.2).
pub(crate) struct Mem {
    pub name: Sym,
    pub path: PathId,
    pub word: TyId,
    pub depth: u64,
    pub pos: Pos,
    pub read: Option<(Agg, Agg)>,
    pub write: Option<(Agg, Agg, Agg)>,
    pub read_at: Option<Here>,
    pub write_at: Option<Here>,
}

/// A child instance: its path, the index of its done instantiation, its statement, and its name.
pub(crate) struct ChildDecl {
    pub path: PathId,
    pub inst: usize,
    pub pos: Pos,
    pub name: String,
}

/// The target of a `:=` binding: an own resource, or an input of the child number `index`. The
/// input names its port by symbol, so a binding copies no name; the lowering renders it.
pub(crate) enum Sink {
    Own {
        kind: Kind,
        ty: Ty,
        path: PathId,
    },
    Child {
        index: usize,
        inst: PathId,
        port: Sym,
        key: Option<u32>,
        ty: Ty,
    },
}

/// A `:=` binding. Its value has the type of the sink, and the lowering takes it leaf by leaf.
pub(crate) struct Bind {
    pub sink: Sink,
    pub value: Agg,
    pub pos: Pos,
}

/// The hardware description of one instantiation, in evaluation order. A combinational
/// module has no domain.
pub(crate) struct Body {
    pub domain: Option<Sym>,
    pub ports: Vec<PortDecl>,
    pub regs: Vec<RegDecl>,
    /// The paths of the wires. Only the tests read them: a wire lowers through its binding.
    #[cfg(test)]
    pub(super) wires: Vec<PathId>,
    pub lets: Vec<Let>,
    pub mems: Vec<Mem>,
    pub children: Vec<ChildDecl>,
    pub binds: Vec<Bind>,
}

impl Body {
    pub(super) fn new(domain: Option<Sym>) -> Body {
        Body {
            domain,
            ports: Vec::new(),
            regs: Vec::new(),
            #[cfg(test)]
            wires: Vec::new(),
            lets: Vec::new(),
            mems: Vec::new(),
            children: Vec::new(),
            binds: Vec::new(),
        }
    }
}

/// The interface of a done instantiation: its emitted name, its ports by their identity, its
/// number of inputs, and its domain. `item` is the module item. Its port families are the static
/// families of the resolver (`Syms::families`), which include a family without an entry, and the
/// families of the public names of its body (`families`).
pub(crate) struct Iface {
    pub name: Name,
    pub(super) ports: BTreeMap<PortId, Port>,
    pub item: usize,
    pub(super) inputs: usize,
    pub domain: Option<Sym>,
    pub(super) families: BTreeSet<Sym>,
}

impl Iface {
    pub(super) fn of(
        name: Name,
        b: &Body,
        item: usize,
        publics: &BTreeMap<PubKey, (Public, Pos, usize)>,
    ) -> Iface {
        let mut ports = BTreeMap::new();
        let mut inputs = 0;
        for (order, q) in b.ports.iter().enumerate() {
            ports.insert(
                (q.sym, q.key),
                Port {
                    sym: q.sym,
                    key: q.key,
                    input: q.input,
                    ty: q.tid,
                    pos: q.pos,
                    order,
                },
            );
            inputs += usize::from(q.input);
        }
        Iface {
            name,
            ports,
            item,
            inputs,
            domain: b.domain,
            families: publics
                .iter()
                .filter(|(_, (form, ..))| matches!(form, Public::Family(_)))
                .map(|(k, _)| k.0)
                .collect(),
        }
    }

    /// Whether a public name of the body is the family `sym`.
    pub(crate) fn declares_family(&self, sym: Sym) -> bool {
        self.families.contains(&sym)
    }
}

/// A done instantiation: its interface, its description, its units, and the position of its
/// module item.
pub(crate) struct Inst {
    pub iface: Iface,
    pub body: Body,
    pub units: u64,
    pub pos: Pos,
}

/// An elaborated design: the done instantiations in the order they finish, the top among
/// them, the position of the top selection, the used fuel, and the fuel that remains for the
/// lowering. It keeps the arenas of the hardware values and of the paths that its
/// descriptions refer to, the table of types and the field names of the struct items (the
/// lowering names the leaves of a record by them), and the text of each symbol. Dropping it is safe on any stack: it
/// holds no recursive value.
pub struct Design {
    pub(crate) insts: Vec<Inst>,
    pub(crate) top: usize,
    pub(crate) pos: Pos,
    pub(super) used: u64,
    pub(crate) left: u64,
    pub(crate) graph: Graph,
    pub(crate) paths: Paths,
    pub(crate) tys: Types,
    pub(crate) field_order: Vec<Vec<Sym>>,
    pub(crate) texts: Vec<String>,
}

impl Design {
    /// The fuel that the elaboration used.
    #[must_use]
    pub fn used(&self) -> u64 {
        self.used
    }

    /// The output of `cost` (section 8) without the charges of the lowering: the total, then
    /// the units of each instantiation, sorted by its emitted name.
    #[cfg(test)]
    pub(crate) fn cost(&self) -> String {
        let lines = self
            .insts
            .iter()
            .map(|i| (encode(&i.iface.name), i.units))
            .collect();
        crate::flatten::cost_lines(self.used, lines)
    }

    /// The lowering of the design to core IR with the fuel that its elaboration leaves.
    /// The lowering recurses over the hardware values, so it runs on a thread with a stack
    /// for the highest of them.
    ///
    /// # Errors
    /// Returns an error if the machine cannot give the stack.
    pub fn lower(&self) -> Result<Result<crate::Lowered, crate::Failure>, StackError> {
        crate::flatten::lower(self)
    }

    /// The emitted names in the order in which the instantiations finish.
    #[cfg(test)]
    #[must_use]
    pub(crate) fn order(&self) -> Vec<String> {
        self.insts.iter().map(|i| encode(&i.iface.name)).collect()
    }

    /// The core names of the named bindings, the registers, the wires, and the children of
    /// the instantiation with the emitted name `module`.
    #[cfg(test)]
    #[must_use]
    pub(crate) fn core_names(&self, module: &str) -> Option<Vec<String>> {
        let i = self
            .insts
            .iter()
            .find(|i| encode(&i.iface.name) == module)?;
        let b = &i.body;
        let paths = b
            .lets
            .iter()
            .map(|l| l.path)
            .chain(b.regs.iter().map(|r| r.path))
            .chain(b.wires.iter().copied())
            .chain(b.children.iter().map(|c| c.path));
        Some(
            paths
                .map(|p| encode(&self.paths.name(p, &self.texts)))
                .collect(),
        )
    }
}
