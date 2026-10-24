// SPDX-License-Identifier: Apache-2.0
//! The work state of the current instantiation.

use super::bind::{Breach, Need};
use super::design::{Body, Here};
use super::public::{PubKey, Public};
use crate::hw::{PortId, Val};
use crate::names::Sym;
use parse::ast::Pos;
use std::collections::BTreeMap;

/// The work of the current instantiation. The resource number indexes `needs`, and the instance
/// number indexes `bound`. The memories are in the body, where `Handle::Mem` indexes them.
/// `inputs` counts the bindings of each child input, with the position and the call frame number of the first one. `dup`
/// holds the first `S018` of a second binding or a second port call by position. `spent` is the
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
}
