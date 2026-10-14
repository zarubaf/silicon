// SPDX-License-Identifier: Apache-2.0
//! The memory port calls of Lean `Source.Eval.portCall` (section 6.2). `read_port(m, addr, en)`
//! and `write_port(m, addr, data, en)` run in this order, and each error is at the call:
//!
//! 1. The node, the callee name, and the copies of the arguments charge first. The memory
//!    handle has the size 1. The caller paid them.
//! 2. The first argument is a raw context, so a memory is never read: it must be a memory
//!    (`S010`).
//! 3. A call inside a guard has an effect that the guard cannot take (`S016`).
//! 4. The typed uses come in the order of the arguments: `addr` at `UInt[A]`, `en` at `Bool`,
//!    and `data` at the word type.
//! 5. The memory records the first request of each kind. A second call runs the same steps and
//!    charges and keeps the first request. Its `S018` waits for the end of the body.
//! 6. `read_port` then charges the struct use of `ReadResponse[T]`, checks the depth of the
//!    response, and charges its zero size. The response refers to the word and to `m$0rvalid`,
//!    so it makes no leaf walk. `write_port` gives `()`.

use super::{Evaluator, Out, Res, fail};
use crate::Code;
use crate::agg::{Agg, Base};
use crate::hw::{Handle, Op, Seen, Val};
use crate::names::Role;
use crate::types::{Ty, TyId};
use crate::value::Value;
use parse::ast::{Item, Pos};
use resolve::Prelude;

/// The address width of a memory of the depth `n`: `max(1, ceil(log2 n))` (section 7.6).
pub(crate) fn addr_width(n: u64) -> u32 {
    (u64::BITS - n.saturating_sub(1).leading_zeros()).max(1)
}

impl Evaluator<'_> {
    /// The call at `pos` of the port function `builtin` named `g`, with the arguments `vs` in
    /// the order of the parameters. The caller charged the node, the name, and the copies.
    pub(super) fn port_call(
        &mut self,
        pos: Pos,
        g: &str,
        builtin: Prelude,
        mut vs: Vec<Out>,
    ) -> Res<Option<Out>> {
        let id = match vs.first().map(|o| self.store.seen(o)) {
            Some(Seen::Handle(Handle::Mem(id))) => *id,
            first => {
                let text = first.map_or_else(|| "nothing".to_owned(), |s| self.text(s));
                return fail(Code::S010, pos, format!("`{g}` needs a memory, not {text}"));
            }
        };
        if let Some(guard) = self.guard {
            return fail(Code::S016, pos, guard.effect(g));
        }
        let Some(mem) = self.mem(id) else {
            return fail(Code::S010, pos, format!("`{g}` needs a memory"));
        };
        let (path, word, depth) = (mem.path, mem.word, mem.depth);
        let rest = vs.split_off(1);
        let addr_ty = self.tys.mk(Ty::UInt(addr_width(depth)));
        let bool_ty = self.tys.mk(Ty::Bool);
        let unaccepted = || format!("`{g}` does not accept its arguments");
        match builtin {
            Prelude::ReadPort => {
                let Ok([x, e]) = <[Out; 2]>::try_from(rest) else {
                    return fail(Code::S010, pos, unaccepted());
                };
                let addr = self.request_part(pos, addr_ty, x)?;
                let en = self.request_part(pos, bool_ty, e)?;
                if let Some(mem) = self.mem_mut(id) {
                    if mem.read.is_some() {
                        mem.dup = Some(second(mem.dup, pos, "read_port"));
                    } else {
                        mem.read = Some((addr, en));
                    }
                }
                self.response(pos, path, word).map(Some)
            }
            Prelude::WritePort => {
                let Ok([x, y, e]) = <[Out; 3]>::try_from(rest) else {
                    return fail(Code::S010, pos, unaccepted());
                };
                let addr = self.request_part(pos, addr_ty, x)?;
                let data = self.request_part(pos, word, y)?;
                let en = self.request_part(pos, bool_ty, e)?;
                if let Some(mem) = self.mem_mut(id) {
                    if mem.write.is_some() {
                        mem.dup = Some(second(mem.dup, pos, "write_port"));
                    } else {
                        mem.write = Some((addr, data, en));
                    }
                }
                Ok(Some(Out::Made(Val::Static(Value::Unit))))
            }
            _ => fail(Code::S010, pos, unaccepted()),
        }
    }

    /// The typed use of `out` at `t` at `pos` as a part of a request. It is a static value, a
    /// hardware value, or a hardware aggregate.
    fn request_part(&mut self, pos: Pos, t: TyId, out: Out) -> Res<Agg> {
        let v = self.read_use(pos, t, true, out)?;
        match Agg::of_val(v) {
            Ok(a) => Ok(a),
            Err(v) => fail(
                Code::S010,
                pos,
                format!("{} is not data", self.text(v.seen())),
            ),
        }
    }

    /// The response of `read_port` at the word type `word` of the memory with the path `path`:
    /// a record of `ReadResponse[T]`. `data` refers to the word at the offset 0, and `valid`
    /// to `m$0rvalid`. The struct use charges as any struct use, the depth of the type is
    /// checked, and the zero size of the type charges before the response exists.
    fn response(&mut self, pos: Pos, path: crate::names::PathId, word: TyId) -> Res<Out> {
        let file = self.file;
        let i = file.ast().len().saturating_sub(1);
        let Some(Item::Struct {
            name,
            params,
            fields,
            ..
        }) = file.ast().get(i)
        else {
            return fail(
                Code::S010,
                pos,
                "the prelude struct `ReadResponse` is missing".to_owned(),
            );
        };
        let arg = Out::Made(Val::Static(Value::Type(word)));
        let ty = self.spec_of(pos, (i, name, params, fields), vec![arg])?;
        self.bounded(pos, self.tys.zero_depth(ty))?;
        self.fuel
            .pay_int(&self.tys.meta(ty).zero_size)
            .map_err(super::at(pos))?;
        let data = self.part_of(pos, Base::Word(path, 0), word)?;
        let valid_path = self
            .paths
            .push(path, crate::names::Step::Role(Role::Rvalid));
        let valid = Agg::Hw(
            self.graph
                .mk(pos, Ty::Bool, Op::Ref(valid_path), Vec::new()),
        );
        match Agg::node(&self.graph, &self.tys, ty, vec![data, valid]) {
            Some(node) => Ok(Out::Made(node.into_val())),
            None => fail(
                Code::S010,
                pos,
                "the response has the wrong shape".to_owned(),
            ),
        }
    }
}

/// The earlier of the recorded second call and this one, with the callee.
fn second(old: Option<(Pos, &'static str)>, pos: Pos, g: &'static str) -> (Pos, &'static str) {
    #[cfg(test)]
    crate::counters::add(crate::counters::Count::Seconds, 1);
    match old {
        Some((at, port)) if pos >= at => (at, port),
        _ => (pos, g),
    }
}
