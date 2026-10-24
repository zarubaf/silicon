// SPDX-License-Identifier: Apache-2.0
//! The binding rule of the resources and the texts of `S018` (Lean `Elab`, section 6.2 of the
//! front-end spec). A record of `S018` holds symbols, item indices, and positions, so a binding
//! records in constant work, and the winner renders its text once.

use super::design::{Bind, Here, Sink};
use crate::Code;
use crate::agg::Agg;
use crate::eval::{Evaluator, Res, fail};
use crate::hw::{Handle, Kind, Port, Val};
use crate::names::{PathId, Sym, entry_text};
use crate::ops::str_text;
use crate::types::TyId;
use parse::ast::{Item, Pos};

/// A resource that needs one binding: its name, its declaration, its bindings, and the position
/// of the first one with its call frame number. An own output (`port`) has its public name. An
/// output with an `as` key has its `binder` for the fix of its `S018` text.
pub(super) struct Need {
    name: Sym,
    key: Option<u32>,
    port: bool,
    binder: Option<Sym>,
    pos: Pos,
    count: u64,
    first: Option<Here>,
}

/// A resource in an `S018` text (section 6.2): an own resource by its source name, or the input
/// `port` of the child number `child`, which renders as `u.p`. The key of a family entry renders
/// as `x[k]`. An own output (the flag) and a child input have their public name, with the limit of
/// a string in a message.
#[derive(Clone, Copy)]
pub(super) enum Subject {
    Own(Sym, Option<u32>, bool),
    Input {
        child: usize,
        port: Sym,
        key: Option<u32>,
    },
}

/// The data of an `S018` text of section 6.2. A binding or a port call records it with no walk.
/// It holds symbols, indices, positions, and the item `h` of a helper. Its text renders once,
/// for the error that wins. `write` is true for `write_port`.
#[derive(Clone, Copy)]
pub(super) enum Breach {
    Second {
        r: Subject,
        b: Pos,
        d: Pos,
    },
    SecondIn {
        r: Subject,
        h: usize,
    },
    /// An own resource with no binding. An output with an `as` key also names its binder.
    Unbound(Subject, Option<Sym>),
    /// The first child with a free input, by its number.
    Input(usize),
    NoPort {
        mem: usize,
        write: bool,
    },
    Port {
        mem: usize,
        write: bool,
        b: Pos,
    },
    PortIn {
        mem: usize,
        write: bool,
        h: usize,
    },
}

pub(super) fn before(a: Pos, b: Pos) -> bool {
    a < b
}

/// The target of a `:=` binding. It refers, so it charges nothing.
#[derive(Clone)]
pub(super) enum Target {
    Own {
        kind: Kind,
        id: usize,
        ty: TyId,
        path: PathId,
    },
    Child {
        inst: usize,
        path: PathId,
        port: Port,
    },
}

impl Evaluator<'_> {
    /// A resource that needs one binding. An output has the `binder` of its `as` key for its
    /// `S018` text. The result is its handle.
    pub(super) fn resource(
        &mut self,
        kind: Kind,
        path: PathId,
        tid: TyId,
        pos: Pos,
        (name, key): (Sym, Option<u32>),
        binder: Option<Sym>,
    ) -> Val {
        let id = self.elab.work.needs.len();
        self.elab.work.needs.push(Need {
            name,
            key,
            port: kind == Kind::Output,
            binder,
            pos,
            count: 0,
            first: None,
        });
        Val::Handle(Handle::Res {
            kind,
            id,
            ty: tid,
            path,
        })
    }

    /// The function whose body runs, the `{h}` of the `S018` texts of a helper (section 6.2). A
    /// module body gives none.
    pub(super) fn helper(&self) -> Option<usize> {
        matches!(self.file.ast().get(self.item), Some(Item::Fn { .. })).then_some(self.item)
    }

    /// Records the `S018` data `x` at `pos`. The first by position wins, and a tie keeps the
    /// first recorded one (section 6.2).
    pub(super) fn breach(&mut self, pos: Pos, x: Breach) {
        let w = &mut self.elab.work;
        w.dup = Some(match w.dup {
            Some((q, y)) if !before(pos, q) => (q, y),
            _ => (pos, x),
        });
    }

    /// The `S018` data of a second binding or a second port call at `pos`, whose first one is at
    /// `first.0` in the call frame `first.1`. When both are at `pos`, one `:=` or call runs
    /// again. When the first one ran in another call, the text names the function. A repeat in
    /// one call keeps the plain text (section 6.2).
    pub(super) fn again(&self, pos: Pos, first: Here) -> Option<usize> {
        if first.0 == pos && first.1 != self.call {
            self.helper()
        } else {
            None
        }
    }

    /// Records the second port call of the memory number `id` at `pos`, if its first call of
    /// that kind exists. The result tells if the call is a second one.
    pub(in crate::eval) fn second_call(&mut self, pos: Pos, id: usize, write: bool) -> bool {
        let Some(mem) = self.mem(id) else {
            return false;
        };
        let Some(b) = (if write { mem.write_at } else { mem.read_at }) else {
            return false;
        };
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Seconds, 1);
        let x = match self.again(pos, b) {
            Some(h) => Breach::PortIn { mem: id, write, h },
            None => Breach::Port {
                mem: id,
                write,
                b: b.0,
            },
        };
        self.breach(pos, x);
        true
    }

    /// The `S018` data of the second binding at `pos` of the resource `subject`, whose first
    /// binding is at `first` and whose declaration is at `decl`.
    pub(super) fn second_binding(
        &self,
        pos: Pos,
        subject: Subject,
        first: Here,
        decl: Pos,
    ) -> Breach {
        match self.again(pos, first) {
            Some(h) => Breach::SecondIn { r: subject, h },
            None => Breach::Second {
                r: subject,
                b: first.0,
                d: decl,
            },
        }
    }

    /// Records the binding of `t` to `value`. The second binding of one target is an `S018`,
    /// and the first binding keeps its position for its text.
    pub(super) fn bind_target(&mut self, pos: Pos, t: Target, value: Agg) {
        let here = (pos, self.call);
        let sink = match t {
            Target::Own { kind, id, ty, path } => {
                let need = self.elab.work.needs.get(id);
                let seen =
                    need.map(|n| (n.count, n.first, Subject::Own(n.name, n.key, n.port), n.pos));
                if let Some((count, first, subject, decl)) = seen {
                    if count == 1 {
                        let x = self.second_binding(pos, subject, first.unwrap_or(here), decl);
                        self.breach(pos, x);
                    }
                    if let Some(n) = self.elab.work.needs.get_mut(id) {
                        n.count += 1;
                        n.first = n.first.or(Some(here));
                    }
                }
                let ty = self.tys.get(ty).clone();
                Sink::Own { kind, ty, path }
            }
            Target::Child { inst, path, port } => {
                let key = (inst, port.id());
                let (count, first) = self
                    .elab
                    .work
                    .inputs
                    .get(&key)
                    .copied()
                    .unwrap_or((0, here));
                if count == 0
                    && let Some(n) = self.elab.work.bound.get_mut(inst)
                {
                    *n += 1;
                }
                self.elab.work.inputs.insert(key, (count + 1, first));
                if count == 1 {
                    let decl = self.elab.work.child(inst).map_or(pos, |child| child.pos);
                    let subject = Subject::Input {
                        child: inst,
                        port: port.sym,
                        key: port.key,
                    };
                    let x = self.second_binding(pos, subject, first, decl);
                    self.breach(pos, x);
                }
                let ty = self.tys.get(port.ty).clone();
                Sink::Child {
                    index: inst,
                    inst: path,
                    port: port.sym,
                    key: port.key,
                    ty,
                }
            }
        };
        self.elab.work.add_bind(Bind { sink, value, pos });
    }

    /// The binding rule at the end of a body. A missing binding of an own resource is at its
    /// declaration, and one of a child input is at the `instance` statement. The counts
    /// select the first child with a free input, so only the interface of that child is
    /// searched. The records compete by position, and the text of the winner renders once
    /// (section 6.2).
    pub(super) fn bindings(&self) -> Res<()> {
        let work = &self.elab.work;
        let first_of = |old: Option<(Pos, Breach)>, at: Pos, x: Breach| match old {
            Some(o) if !before(at, o.0) => Some(o),
            _ => Some((at, x)),
        };
        let mut first = work.dup;
        for need in &work.needs {
            if need.count == 0 {
                let r = Subject::Own(need.name, need.key, need.port);
                first = first_of(first, need.pos, Breach::Unbound(r, need.binder));
            }
        }
        for (k, mem) in work.body.mems.iter().enumerate() {
            if mem.read.is_none() || mem.write.is_none() {
                let x = Breach::NoPort {
                    mem: k,
                    write: mem.read.is_some(),
                };
                first = first_of(first, mem.pos, x);
            }
        }
        let mut free: Option<(Pos, usize)> = None;
        for (k, child) in work.body.children.iter().enumerate() {
            let inputs = self.elab.done.get(child.inst).map_or(0, |i| i.iface.inputs);
            if work.bound.get(k).copied().unwrap_or(0) < inputs
                && free.is_none_or(|(at, _)| before(child.pos, at))
            {
                free = Some((child.pos, k));
            }
        }
        if let Some((at, k)) = free {
            first = first_of(first, at, Breach::Input(k));
        }
        let Some((pos, x)) = first else {
            return Ok(());
        };
        fail(Code::S018, pos, self.breach_text(x))
    }

    /// The text of the `S018` of the first child number `k` with a free input: the free input
    /// with the first source position.
    pub(super) fn free_input_text(&self, k: usize) -> String {
        let work = &self.elab.work;
        let text = |sym: Sym| self.syms.texts.get(sym).map_or("", String::as_str);
        let iface = work
            .child(k)
            .and_then(|child| self.elab.done.get(child.inst))
            .map(|i| &i.iface);
        let port = iface.and_then(|i| {
            i.ports
                .values()
                .filter(|q| q.input && !work.inputs.contains_key(&(k, q.id())))
                .min_by_key(|q| (q.pos.line, q.pos.col, q.order))
        });
        let name = port.map_or_else(String::new, |q| str_text(&entry_text(text(q.sym), q.key)));
        let inst = work.child(k).map_or("", |c| c.name.as_str());
        format!(
            "the input `{name}` of the instance `{inst}` has no binding; \
             bind it with `{inst}.{name} := ...;`"
        )
    }

    /// The text of the `S018` data `x` (section 6.2).
    pub(super) fn breach_text(&self, x: Breach) -> String {
        let work = &self.elab.work;
        let sym_text = |sym: Sym| self.syms.texts.get(sym).map_or("", String::as_str);
        let at = |p: Pos| format!("{}:{}", p.line, p.col);
        let subject = |r: Subject| match r {
            Subject::Own(sym, key, true) => str_text(&entry_text(sym_text(sym), key)),
            Subject::Own(sym, key, false) => entry_text(sym_text(sym), key),
            Subject::Input { child, port, key } => {
                let u = work.child(child).map_or("", |c| c.name.as_str());
                format!("{u}.{}", str_text(&entry_text(sym_text(port), key)))
            }
        };
        let mem_name = |k: usize| work.mem(k).map_or("", |m| sym_text(m.name));
        let call = |write: bool| if write { "write_port" } else { "read_port" };
        let item = |h: usize| self.item_name(h);
        let text = match x {
            Breach::Second { r, b, d } => format!(
                "`{}` has a second binding; the first binding is at {}, and the declaration is \
                 at {}; remove one of the two bindings",
                subject(r),
                at(b),
                at(d)
            ),
            Breach::SecondIn { r, h } => format!(
                "`{}` has a second binding, because the `:=` in `{}` runs again for it; run \
                 the `:=` once for each resource, for example with one call of `{}` for each",
                subject(r),
                item(h),
                item(h)
            ),
            Breach::Unbound(r, Some(binder)) => format!(
                "the output `{}` has no binding; bind its binder with `{} := ...;`, or remove its \
                 declaration",
                subject(r),
                sym_text(binder)
            ),
            Breach::Unbound(r, None) => {
                let r = subject(r);
                format!(
                    "`{r}` has no binding; bind it with `{r} := ...;`, or remove its declaration"
                )
            }
            Breach::Input(k) => self.free_input_text(k),
            Breach::NoPort { mem, write } => format!(
                "the memory `{}` has no `{}`; call `{}` on it once, or remove the memory",
                mem_name(mem),
                call(write),
                call(write)
            ),
            Breach::Port {
                mem,
                write: false,
                b,
            } => format!(
                "the memory `{}` has a second `read_port`; the first call is at {}; call \
                 `read_port` once and keep its response in a `let`",
                mem_name(mem),
                at(b)
            ),
            Breach::Port {
                mem,
                write: true,
                b,
            } => format!(
                "the memory `{}` has a second `write_port`; the first call is at {}; make one \
                 call, and select its address, data, and enable with a hardware `if`",
                mem_name(mem),
                at(b)
            ),
            Breach::PortIn {
                mem,
                write: false,
                h,
            } => format!(
                "the memory `{}` has a second `read_port`, because the call in `{}` runs again \
                 for it; run the call once for each memory, for example with one call of `{}` \
                 for each",
                mem_name(mem),
                item(h),
                item(h)
            ),
            Breach::PortIn {
                mem,
                write: true,
                h,
            } => format!(
                "the memory `{}` has a second `write_port`, because the call in `{}` runs again \
                 for it; run the call once for each memory, for example with one call of `{}` \
                 for each",
                mem_name(mem),
                item(h),
                item(h)
            ),
        };
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::TextBytes, text.len() as u64);
        text
    }
}
