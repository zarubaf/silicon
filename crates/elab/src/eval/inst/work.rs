// SPDX-License-Identifier: Apache-2.0
//! The work state of the current instantiation.

use super::bind::{Breach, Subject};
use super::design::{Bind, Body, ChildDecl, Here, Inst, Mem, PortDecl, RegDecl};
use super::public::{PubKey, Public};
use crate::hw::{PortId, Val};
#[cfg(test)]
use crate::names::PathId;
use crate::names::Sym;
use parse::ast::Pos;
use std::collections::BTreeMap;

/// A resource that needs one binding: its name, its declaration, its bindings, and the position
/// of the first one with its call frame number. An own output (`port`) has its public name. An
/// output with an `as` key has its `binder` for the fix of its `S018` text.
struct Need {
    name: Sym,
    key: Option<u32>,
    port: bool,
    binder: Option<Sym>,
    pos: Pos,
    count: u64,
    first: Option<Here>,
}

/// Whether the position `a` is before `b`.
fn before(a: Pos, b: Pos) -> bool {
    a < b
}

/// The work of the current instantiation. The resource number indexes `needs`, and the instance
/// number indexes `bound`. The memories are in the body, where `Handle::Mem` indexes them.
/// `inputs` counts the bindings of each child input, with the position and the call frame
/// number of the first one. `dup` holds the first `S018` of a second binding or a second port call by position. `spent` is the
/// fuel of the new children. `entries` holds the declared family entries by the symbol of the
/// public name and the key: the value of each entry and the position of its declaration. A family
/// binder has no frame slot. `publics` is the table of the public names of the owner. It holds the
/// form of each name by its symbol, with the position and the call frame number of its first
/// declaration. `owner` is the module item of the instantiation, whose static families the table
/// does not copy (`public_of`).
pub(super) struct Work {
    pub(super) body: Body,
    needs: Vec<Need>,
    bound: Vec<usize>,
    inputs: BTreeMap<(usize, PortId), (u64, Here)>,
    pub(super) entries: BTreeMap<(Sym, u32), (Val, Pos)>,
    pub(super) publics: BTreeMap<PubKey, (Public, Pos, usize)>,
    pub(super) owner: usize,
    dup: Option<(Pos, Breach)>,
    pub(super) spent: u64,
}

impl Work {
    pub(super) fn new(domain: Option<Sym>, owner: usize) -> Work {
        Work {
            body: Body::new(domain),
            needs: Vec::new(),
            bound: Vec::new(),
            inputs: BTreeMap::new(),
            entries: BTreeMap::new(),
            publics: BTreeMap::new(),
            owner,
            dup: None,
            spent: 0,
        }
    }

    /// Whether the instantiation has a clock domain.
    pub(super) fn clocked(&self) -> bool {
        self.body.domain.is_some()
    }

    /// Declares a port.
    pub(super) fn add_port(&mut self, port: PortDecl) {
        self.body.ports.push(port);
    }

    /// Declares a register.
    pub(super) fn add_reg(&mut self, reg: RegDecl) {
        self.body.regs.push(reg);
    }

    /// Records the path of a wire. Only the tests read it.
    #[cfg(test)]
    pub(super) fn add_wire(&mut self, path: PathId) {
        self.body.wires.push(path);
    }

    /// Records a `:=` binding.
    pub(super) fn add_bind(&mut self, bind: Bind) {
        self.body.binds.push(bind);
    }

    /// Declares a memory. The result is its number.
    pub(super) fn add_mem(&mut self, mem: Mem) -> usize {
        self.body.mems.push(mem);
        self.body.mems.len() - 1
    }

    /// The memory number `id`.
    pub(super) fn mem(&self, id: usize) -> Option<&Mem> {
        self.body.mems.get(id)
    }

    /// The memory number `id`, for a request.
    pub(super) fn mem_mut(&mut self, id: usize) -> Option<&mut Mem> {
        self.body.mems.get_mut(id)
    }

    /// Declares a child instance, with no binding of its inputs. The result is its number.
    pub(super) fn add_child(&mut self, child: ChildDecl) -> usize {
        self.body.children.push(child);
        self.bound.push(0);
        self.body.children.len() - 1
    }

    /// The child instance number `k`.
    pub(super) fn child(&self, k: usize) -> Option<&ChildDecl> {
        self.body.children.get(k)
    }

    /// Declares a resource that needs one binding. The result is its number.
    pub(super) fn add_need(
        &mut self,
        (name, key): (Sym, Option<u32>),
        port: bool,
        binder: Option<Sym>,
        pos: Pos,
    ) -> usize {
        self.needs.push(Need {
            name,
            key,
            port,
            binder,
            pos,
            count: 0,
            first: None,
        });
        self.needs.len() - 1
    }

    /// Counts a binding of the own resource number `id` at `here`. The result is its state before
    /// the binding: the count, the first binding (`here` for the first one), the subject of its
    /// `S018` text, and its declaration.
    pub(super) fn bind_own(&mut self, id: usize, here: Here) -> Option<(u64, Here, Subject, Pos)> {
        let n = self.needs.get_mut(id)?;
        let seen = (
            n.count,
            n.first.unwrap_or(here),
            Subject::Own(n.name, n.key, n.port),
            n.pos,
        );
        n.count += 1;
        n.first = n.first.or(Some(here));
        Some(seen)
    }

    /// Counts a binding of the input `port` of the child number `inst` at `here`. The result is
    /// the count before the binding and the first binding (`here` for the first one).
    pub(super) fn bind_input(&mut self, inst: usize, port: PortId, here: Here) -> (u64, Here) {
        let key = (inst, port);
        let (count, first) = self.inputs.get(&key).copied().unwrap_or((0, here));
        if count == 0
            && let Some(n) = self.bound.get_mut(inst)
        {
            *n += 1;
        }
        self.inputs.insert(key, (count + 1, first));
        (count, first)
    }

    /// Whether the input `port` of the child number `k` has a binding.
    pub(super) fn has_input(&self, k: usize, port: PortId) -> bool {
        self.inputs.contains_key(&(k, port))
    }

    /// Records the `S018` data `x` at `pos`. The first by position wins, and a tie keeps the
    /// first recorded one (section 6.2).
    pub(super) fn record_breach(&mut self, pos: Pos, x: Breach) {
        self.dup = Some(match self.dup {
            Some((q, y)) if !before(pos, q) => (q, y),
            _ => (pos, x),
        });
    }

    /// The first `S018` of the binding rule at the end of a body, if any. A missing binding of an
    /// own resource is at its declaration, and one of a child input is at the `instance`
    /// statement. The counts select the first child with a free input. The records compete by
    /// position (section 6.2). `done` holds the interfaces of the done instantiations.
    pub(super) fn first_breach(&self, done: &[Inst]) -> Option<(Pos, Breach)> {
        let first_of = |old: Option<(Pos, Breach)>, at: Pos, x: Breach| match old {
            Some(o) if !before(at, o.0) => Some(o),
            _ => Some((at, x)),
        };
        let mut first = self.dup;
        for need in &self.needs {
            if need.count == 0 {
                let r = Subject::Own(need.name, need.key, need.port);
                first = first_of(first, need.pos, Breach::Unbound(r, need.binder));
            }
        }
        for (k, mem) in self.body.mems.iter().enumerate() {
            if mem.read.is_none() || mem.write.is_none() {
                let x = Breach::NoPort {
                    mem: k,
                    write: mem.read.is_some(),
                };
                first = first_of(first, mem.pos, x);
            }
        }
        let mut free: Option<(Pos, usize)> = None;
        for (k, child) in self.body.children.iter().enumerate() {
            let inputs = done.get(child.inst).map_or(0, |i| i.iface.inputs);
            if self.bound.get(k).copied().unwrap_or(0) < inputs
                && free.is_none_or(|(at, _)| before(child.pos, at))
            {
                free = Some((child.pos, k));
            }
        }
        if let Some((at, k)) = free {
            first = first_of(first, at, Breach::Input(k));
        }
        first
    }
}
