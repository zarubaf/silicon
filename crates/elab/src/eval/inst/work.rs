// SPDX-License-Identifier: Apache-2.0
//! The work state of the current instantiation.

use super::bind::{Breach, Need};
use super::design::{Bind, Body, ChildDecl, Here, Mem, PortDecl, RegDecl};
use super::public::{PubKey, Public};
use crate::hw::{PortId, Val};
#[cfg(test)]
use crate::names::PathId;
use crate::names::Sym;
use parse::ast::Pos;
use std::collections::BTreeMap;

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
    pub(super) needs: Vec<Need>,
    pub(super) bound: Vec<usize>,
    pub(super) inputs: BTreeMap<(usize, PortId), (u64, Here)>,
    pub(super) entries: BTreeMap<(Sym, u32), (Val, Pos)>,
    pub(super) publics: BTreeMap<PubKey, (Public, Pos, usize)>,
    pub(super) owner: usize,
    pub(super) dup: Option<(Pos, Breach)>,
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
}
