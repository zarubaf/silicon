// SPDX-License-Identifier: Apache-2.0
//! The implicit read of the data contexts of design section 9.2 (Lean `Eval.baseData`, `data`,
//! and `dataAt`). A register, a wire, and an own output give a reference to their name, in its
//! normal form. A container of a type with the handle flag charges its recursive size, and then
//! each handle leaf reads in packing order. The walks keep their own stacks.

use super::{Evaluator, Opnd, Out, Res, fail, no_type};
use crate::Code;
use crate::agg::{Agg, Base};
use crate::hw::{Handle, Seen, Val};
use crate::names::PathId;
use crate::types::{Ty, TyId};
use parse::ast::Pos;

/// A step of the read of a container of handles: read a part under some nodes, or make a node of
/// the last `n` results at the data type `t`.
enum Read {
    Visit(Agg, u64),
    Build(TyId, usize),
}

impl Evaluator<'_> {
    /// The text "`read` of an input" of the input `port` of the child at `path` (section 6.2).
    pub(super) fn input_text(&self, path: PathId, port: &crate::hw::Port) -> String {
        let name = self.syms.texts.get(port.sym).map_or("", String::as_str);
        format!(
            "the input `{name}` of `{}` is a target only; read the value that you bind to it",
            self.paths.source(path, &self.syms.texts)
        )
    }

    /// The read of the handle `h` at `pos` in a data context, under `above` nodes of a container
    /// (Lean `readHandle`). A register, a wire, and an own output read by `read_agg`, so the
    /// depth check comes first. A child input is never read (`S017`). A memory and an instance
    /// are not data (`S010`), and their texts of section 6.2 name the fix. A domain is not data.
    fn read_handle(&mut self, pos: Pos, above: u64, h: &Handle) -> Res<Agg> {
        match h {
            Handle::Res { ty, path, .. } => self.read_agg(pos, Base::Name(*path), *ty, above),
            Handle::Input { path, port, .. } => fail(Code::S017, pos, self.input_text(*path, port)),
            Handle::Mem(id) => {
                let r = self
                    .mem(*id)
                    .map_or_else(String::new, |m| self.paths.source(m.path, &self.syms.texts));
                fail(
                    Code::S010,
                    pos,
                    format!("`{r}` is a memory, not data; read a word with `read_port`"),
                )
            }
            Handle::Inst { path, .. } => {
                let r = self.paths.source(*path, &self.syms.texts);
                fail(
                    Code::S010,
                    pos,
                    format!("`{r}` is an instance, not data; read its outputs as `{r}.q`"),
                )
            }
            Handle::Domain(_) => fail(Code::S010, pos, "a domain is not data".to_owned()),
        }
    }

    /// The data of a result at a use that only selects from it (Lean `baseData`): the base of an
    /// index, of a selector, and of a field, and the argument of `len`. A register, a wire, and
    /// an own output give a reference to their name in its normal form: the implicit read. Thus a
    /// scalar is hardware, and an aggregate is a lazy reference with no charge. A container of
    /// handles passes, so the selection reads only the part that it selects.
    pub(super) fn base_data(&mut self, pos: Pos, out: Out) -> Res<Opnd> {
        match self.store.seen(&out) {
            Seen::Static(_) | Seen::Agg(_) => Ok(Opnd::Static(out)),
            Seen::Hw(h) => Ok(Opnd::Hw(h)),
            Seen::Pending(q, _) => no_type(q),
            Seen::Handle(h) => {
                let h = h.clone();
                let a = self.read_handle(pos, 0, &h)?;
                Ok(Opnd::of_out(Out::Made(a.into_val())))
            }
        }
    }

    /// The data of a result at a use that reads it (Lean `data`, section 9.2). A handle reads by
    /// `base_data`. A container of a type with the handle flag charges its recursive size first.
    /// Then each leaf reads in packing order (`read_container`), and the error is at `pos`. An
    /// empty container of memories, instances, or inputs has no leaf to report at. Thus a result
    /// that keeps the flag is `S010` with the text "Handles as data". Another value is data
    /// already.
    pub(super) fn data(&mut self, pos: Pos, out: Out) -> Res<Opnd> {
        let flagged = match self.store.seen(&out) {
            Seen::Agg(a) => a.stored_ty().filter(|t| t.holds_handles()),
            _ => None,
        };
        let Some(t) = flagged else {
            return self.base_data(pos, out);
        };
        let size = self.size(&out);
        self.charge(pos, size)?;
        let Val::Agg(root) = self.store.take(out) else {
            return fail(Code::S010, pos, "a container is expected".to_owned());
        };
        let read = self.read_container(pos, *root)?;
        if read.stored_ty().is_some_and(TyId::holds_handles) {
            return fail(Code::S010, pos, self.handles_data_text(t));
        }
        Ok(Opnd::of_out(Out::Made(read.into_val())))
    }

    /// The data of a result at a typed use at the type `t` (Lean `dataAt`). A position of a type
    /// with the handle flag is `raw` (section 9.2), so it reads nothing: a handle and a container
    /// keep their handles. A position of another type reads each handle (`data`).
    pub(super) fn data_at(&mut self, pos: Pos, t: TyId, out: Out) -> Res<Opnd> {
        if t.holds_handles() {
            Ok(Opnd::of_out(out))
        } else {
            self.data(pos, out)
        }
    }

    /// The text "Handles as data" of section 6.2 for a value of the type `t`.
    fn handles_data_text(&self, t: TyId) -> String {
        format!(
            "a `data` context does not read `{}`, a type that holds a memory, an instance, or an \
             input; read the data of each element",
            self.tys.text(t)
        )
    }

    /// The text of a record or a list of handles `ty` in a data context (section 6.2).
    fn handles_text(&self, ty: TyId, list: bool) -> String {
        let t = self.tys.text(ty);
        if list {
            format!(
                "a `data` context does not read the list of handles `{t}`; read each element, \
                 for example `read(hs[0])`"
            )
        } else {
            format!(
                "a `data` context does not read the record of handles `{t}`; construct the data \
                 record from the fields, for example `P(read(h.a), read(h.b))`"
            )
        }
    }

    /// The read of the container of handles `root` (Lean `readPart`). The walk visits the parts
    /// in packing order. It does not enter a part of a type without the handle flag, because that
    /// part is data already. A record node of handles and a list node are `S010`. A handle leaf
    /// reads by `read_handle`, so its depth check comes first, and then a reference charges the
    /// zero size of its type. The result is a new value of the data type.
    fn read_container(&mut self, pos: Pos, root: Agg) -> Res<Agg> {
        let mut done: Vec<Agg> = Vec::new();
        let mut work = vec![Read::Visit(root, 0)];
        while let Some(step) = work.pop() {
            #[cfg(test)]
            crate::counters::add(crate::counters::Count::Read, 1);
            match step {
                Read::Visit(Agg::Handle(h), above) => {
                    let a = self.read_handle(pos, above, &h)?;
                    if matches!(a, Agg::Ref(..)) {
                        let size = a.size(&self.graph, &self.tys);
                        self.charge(pos, u128::from(size))?;
                    }
                    done.push(a);
                }
                Read::Visit(Agg::Record(n, _), _) if n.ty.holds_handles() => {
                    return fail(Code::S010, pos, self.handles_text(n.ty, false));
                }
                Read::Visit(Agg::List(n, _), _) => {
                    return fail(Code::S010, pos, self.handles_text(n.ty, true));
                }
                Read::Visit(Agg::Array(n, mut p) | Agg::Tuple(n, mut p), above)
                    if n.ty.holds_handles() =>
                {
                    let ty = self.data_ty(pos, n.ty)?;
                    let parts = std::mem::take(&mut p.0);
                    work.push(Read::Build(ty, parts.len()));
                    work.extend(parts.into_iter().rev().map(|x| Read::Visit(x, above + 1)));
                }
                Read::Visit(a, _) => done.push(a),
                Read::Build(ty, n) => {
                    let xs = done.split_off(done.len().saturating_sub(n));
                    let Some(node) = Agg::node(&self.graph, &self.tys, ty, xs) else {
                        return fail(Code::S010, pos, "the part has the wrong shape".to_owned());
                    };
                    done.push(node);
                }
            }
        }
        match done.pop() {
            Some(a) => Ok(a),
            None => fail(Code::S010, pos, "the container has no value".to_owned()),
        }
    }

    /// The data type of the type `t` with the handle flag (Lean `dataTy`): each `Reg[T]` and
    /// `Wire[T]` in an array or a tuple becomes `T`. Another type stays. A type without the flag
    /// is data already, and a done type is read from its entry, so a type is made once and the
    /// read of `N` containers of one type makes no type again. The walk keeps its own stack.
    fn data_ty(&mut self, pos: Pos, t: TyId) -> Res<TyId> {
        let mut work = vec![(t, false)];
        while let Some((u, ready)) = work.pop() {
            if !u.holds_handles() || self.data_tys.contains_key(&u) {
                continue;
            }
            if !ready {
                work.push((u, true));
                match self.tys.get(u) {
                    Ty::Array(e, _) => work.push((*e, false)),
                    Ty::Tuple(ts) => {
                        #[cfg(test)]
                        crate::counters::add(crate::counters::Count::Read, ts.len() as u64);
                        work.extend(ts.iter().map(|p| (*p, false)));
                    }
                    _ => {}
                }
                continue;
            }
            #[cfg(test)]
            crate::counters::add(crate::counters::Count::Read, 1);
            let made = match self.tys.get(u).clone() {
                Ty::Reg(x) | Ty::Wire(x) => x,
                Ty::Array(e, n) => {
                    let e = self.data_of(pos, e)?;
                    self.tys.array(e, n)
                }
                Ty::Tuple(ts) => {
                    let ts = ts
                        .iter()
                        .map(|p| self.data_of(pos, *p))
                        .collect::<Res<Vec<_>>>()?;
                    self.tys.tuple(ts)
                }
                _ => u,
            };
            self.data_tys.insert(u, made);
        }
        self.data_of(pos, t)
    }

    /// The data type of `t` once `data_ty` made it. A type with the handle flag that has no entry
    /// breaks the order of the walk, so it is an error at `pos`.
    fn data_of(&self, pos: Pos, t: TyId) -> Res<TyId> {
        if !t.holds_handles() {
            return Ok(t);
        }
        match self.data_tys.get(&t) {
            Some(made) => Ok(*made),
            None => fail(Code::S010, pos, "the data type was not made".to_owned()),
        }
    }
}
