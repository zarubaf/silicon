// SPDX-License-Identifier: Apache-2.0
//! The calls of Lean `Source.Eval`: a function item, a prelude function, and a type
//! constructor. A call charges its callee name, evaluates its arguments, and binds them in a
//! new call frame.

use super::place::Place;
use super::{Evaluator, Names, Opnd, Out, Res, Slot, Tag, at, expr_pos, fail, need};
use crate::Code;
use crate::hw::{Ref, Val};
use crate::names::{Role, Step};
use crate::ops::{self, str_text};
use crate::value::Value;
use parse::ast::{Expr, Ident, Item, NodeId, Param, ParamMode, Pos};
use resolve::{DeclId, Kind, Prelude, Target};

/// What a call binds to a parameter: the result of its argument, or the place of a `mut`
/// actual.
enum Actual {
    Value(Out),
    Place(Place),
}

/// The parameter of the argument number `k` in the evaluation order of a call whose receiver
/// binds at the parameter `bound`: the receiver evaluates first (`bound` is 0 for a plain call).
fn parameter_of(k: usize, bound: usize) -> usize {
    match k {
        0 => bound,
        k if k <= bound => k - 1,
        k => k,
    }
}

/// The values `vs` in the order of the parameters, when the first one is the receiver that
/// binds at the parameter `bound`.
fn in_parameter_order<T>(mut vs: Vec<T>, bound: usize) -> Vec<T> {
    if bound > 0 && !vs.is_empty() {
        let receiver = vs.remove(0);
        vs.insert(bound.min(vs.len()), receiver);
    }
    vs
}

impl Evaluator<'_> {
    /// The call site of the call node or the method node `node`: its number in the pre-order
    /// of its item, from the resolver. A call outside a body runs on static values only, so its
    /// site never names hardware.
    fn site(&self, node: NodeId) -> u64 {
        let site = match self.names {
            Names::Top => self.top.and_then(|t| t.site(node)),
            Names::File => self.file.site(node),
        };
        site.map_or(0, |k| k as u64)
    }

    /// The parameter that the receiver of the method node `node` binds to, from the resolver.
    fn receiver(&self, node: NodeId) -> Option<usize> {
        match self.names {
            Names::Top => self.top.and_then(|t| t.receiver(node)),
            Names::File => self.file.receiver(node),
        }
    }

    /// A call of a function item, a prelude function, or a type.
    pub(super) fn call(
        &mut self,
        pos: Pos,
        node: NodeId,
        f: &Expr,
        xs: &[Expr],
    ) -> Res<Option<Out>> {
        if let Expr::Name {
            pos: fp,
            id: fid,
            name: g,
        } = f
        {
            let args: Vec<&Expr> = xs.iter().collect();
            match self.target(*fid) {
                Some(Target::Decl(id))
                    if matches!(self.file.decl(id).kind, Kind::Fn | Kind::Module) =>
                {
                    return self.call_fn(pos, node, *fp, g, id, &args, 0);
                }
                Some(Target::Prelude(h)) if !h.is_type() => {
                    return self.call_prelude(pos, *fp, g, h, &args, 0);
                }
                _ => {}
            }
        }
        self.construct(pos, f, xs)
    }

    /// A receiver call `recv.name(xs)`: the call of `name` with `recv` at the first parameter
    /// that the resolver recorded. The receiver evaluates first, then the arguments.
    /// The method name charges 1, as the callee name of a call does.
    pub(super) fn method(
        &mut self,
        pos: Pos,
        node: NodeId,
        recv: &Expr,
        name: &Ident,
        xs: &[Expr],
    ) -> Res<Option<Out>> {
        let target = self.target(name.id);
        let Some(bound) = self.receiver(node) else {
            return fail(
                Code::S007,
                pos,
                format!(
                    "`{}` has no parameter without `comptime` for the receiver",
                    name.name
                ),
            );
        };
        let mut args: Vec<&Expr> = Vec::with_capacity(xs.len() + 1);
        args.push(recv);
        args.extend(xs);
        match target {
            Some(Target::Decl(id)) => {
                self.call_fn(pos, node, name.pos, &name.name, id, &args, bound)
            }
            Some(Target::Prelude(h)) => {
                self.call_prelude(pos, name.pos, &name.name, h, &args, bound)
            }
            None => fail(
                Code::S010,
                pos,
                format!("`{}` is not a function", name.name),
            ),
        }
    }

    /// The arguments `xs` of a call in their evaluation order, as the actuals of the
    /// parameters `params`, in the order of the parameters. A `mut` actual resolves its place by
    /// the steps of an assignment target.
    fn actuals(&mut self, params: &[Param], xs: &[&Expr], bound: usize) -> Res<Vec<Actual>> {
        let mut slots: Vec<Option<Actual>> = xs.iter().map(|_| None).collect();
        // The values wait in the store, so that a later actual cannot change them.
        let base = self.store.parked.len();
        let mut values = Vec::with_capacity(xs.len());
        for (k, x) in xs.iter().enumerate() {
            let at = parameter_of(k, bound);
            if params.get(at).is_some_and(|q| q.mode == ParamMode::Mut) {
                let place = Actual::Place(self.place_at(expr_pos(x), Code::S008, x)?);
                if let Some(slot) = slots.get_mut(at) {
                    *slot = Some(place);
                }
            } else {
                let o = self.eval(x)?;
                let o = need(x, o)?;
                self.store.park(o);
                values.push(at);
            }
        }
        for (at, o) in values.into_iter().zip(self.store.resume(base)) {
            if let Some(slot) = slots.get_mut(at) {
                *slot = Some(Actual::Value(o));
            }
        }
        Ok(slots.into_iter().flatten().collect())
    }

    /// A call of a function item. It runs in the call frame `<fn>$<k>c`. A hardware argument
    /// and a hardware result get a core name in that frame. The write-backs of its `mut`
    /// actuals run in the frame of the caller, after the result.
    #[allow(clippy::too_many_arguments)]
    fn call_fn(
        &mut self,
        pos: Pos,
        node: NodeId,
        fp: Pos,
        g: &str,
        id: DeclId,
        xs: &[&Expr],
        bound: usize,
    ) -> Res<Option<Out>> {
        self.charge(fp, 1)?;
        let file = self.file;
        let Some(&i) = self.items.get(&id) else {
            return fail(Code::S010, fp, format!("`{g}` is not a function"));
        };
        let Some(Item::Fn {
            pos: ip,
            comptime,
            name: fn_name,
            params,
            ret,
            body,
        }) = file.ast().get(i)
        else {
            return fail(Code::S010, fp, format!("`{g}` is not a function"));
        };
        if params.len() != xs.len() {
            self.args(xs.iter().copied())?;
            return fail(
                Code::S007,
                pos,
                format!(
                    "`{g}` takes {} argument(s), but it has {}",
                    params.len(),
                    xs.len()
                ),
            );
        }
        let acts = self.actuals(params, xs, bound)?;
        let site = self.site(node);
        let u = self.syms.items.get(i).copied().unwrap_or(0);
        let (result, written) = self.nested(pos, |ev| {
            ev.in_frame(None, |ev| {
                let (path, frame) = ev.frame_of(u, Step::Call(site));
                ev.in_item(i, frame, |ev| {
                    let mut places = Vec::new();
                    for (q, a) in params.iter().zip(acts) {
                        ev.param(pos, *comptime, q, a, &mut places)?;
                    }
                    let rt = ev.type_expr(ret)?;
                    ev.ret = Some(rt);
                    let result = match ev.block(*ip, body, false)? {
                        Some(Val::Hw(h)) => {
                            let role = ev.paths.push(path, Step::Role(Role::Ret));
                            let name = ev.version(Tag::Ret, role);
                            Out::Made(ev.bind_hw(pos, name, h))
                        }
                        Some(v) => Out::Made(v),
                        None => {
                            return fail(
                                Code::S010,
                                pos,
                                format!("`{}` ends without `return`", fn_name.name),
                            );
                        }
                    };
                    Ok((result, ev.finals(places)))
                })
            })
        })?;
        self.write_back(pos, written)?;
        Ok(Some(result))
    }

    /// The final value of each `mut` formal with the place of its actual, in the order of the
    /// parameters. The value leaves the frame of the callee, so it moves and no copy is made.
    fn finals(&mut self, places: Vec<(DeclId, Place)>) -> Vec<(Place, Val)> {
        let mut written = Vec::with_capacity(places.len());
        for (id, place) in places {
            if let Some(slot) = self.store.frame_mut().and_then(|f| f.get_mut(&id)) {
                written.push((
                    place,
                    std::mem::replace(&mut slot.value, Val::Static(Value::Unit)),
                ));
            }
        }
        written
    }

    /// The write-backs of the call at `pos`, in the order of the parameters. Each checks the
    /// mutation rule (`S016`), then the depth of the root, then charges the size of the final
    /// value, then writes it into the live root.
    fn write_back(&mut self, pos: Pos, written: Vec<(Place, Val)>) -> Res<()> {
        for (place, value) in written {
            self.mutation(pos)?;
            // Another value has the type of the place, so it keeps the depth of the root.
            if let Val::Static(v) = &value {
                self.bounded(pos, place.keys.len() as u64 + v.depth())?;
            }
            self.charge(pos, self.seen_size(value.seen()))?;
            self.store_at(pos, pos, &place, value)?;
        }
        Ok(())
    }

    /// Binds a parameter of a call. Its type can use the parameters before it. A static
    /// parameter needs a static argument. A `mut` formal copies its place, after the charge,
    /// and it is a mutable local of the callee.
    fn param(
        &mut self,
        pos: Pos,
        comptime: bool,
        q: &Param,
        actual: Actual,
        places: &mut Vec<(DeclId, Place)>,
    ) -> Res<()> {
        let t = self.type_expr(&q.ty)?;
        let id = self.decl(&q.name)?;
        let (x, mutable) = match actual {
            Actual::Value(v) => {
                self.charge(pos, self.size(&v))?;
                let x = if comptime || q.mode == ParamMode::Comptime {
                    let v = self.settle(pos, t, v)?;
                    Val::Static(self.conform(pos, t, v)?)
                } else {
                    self.conform_val(pos, t, v)?
                };
                (x, false)
            }
            Actual::Place(place) => {
                let part = Out::Ref(Ref {
                    root: place.root,
                    path: place.keys.clone(),
                });
                self.charge(pos, self.size(&part))?;
                let ty = place
                    .ty
                    .or_else(|| self.store.seen(&part).ty(&self.graph, &mut self.tys));
                if ty != Some(t) {
                    let actual = ty
                        .map_or_else(|| self.text(self.store.seen(&part)), |ty| self.tys.text(ty));
                    return fail(
                        Code::S010,
                        pos,
                        format!(
                            "a `mut` actual has the type {actual}, but its formal has {}",
                            self.tys.text(t)
                        ),
                    );
                }
                let x = if comptime {
                    Val::Static(self.static_value(pos, part)?)
                } else {
                    self.store.take(part)
                };
                places.push((id, place));
                (x, true)
            }
        };
        let x = self.named(pos, id, x);
        self.bind(
            id,
            Slot {
                ty: Some(t),
                mutable,
                value: x,
            },
        );
        Ok(())
    }

    fn call_prelude(
        &mut self,
        pos: Pos,
        fp: Pos,
        g: &str,
        builtin: Prelude,
        xs: &[&Expr],
        bound: usize,
    ) -> Res<Option<Out>> {
        self.charge(fp, 1)?;
        match builtin {
            Prelude::Push => return self.push(pos, g, xs),
            Prelude::Pop => return self.pop(pos, g, xs),
            _ => {}
        }
        let vs = in_parameter_order(self.args(xs.iter().copied())?, bound);
        if builtin == Prelude::Len {
            return self.len(pos, vs);
        }
        if builtin == Prelude::DataBits {
            return self.data_bits(pos, g, &vs);
        }
        let mut sizes = 0u128;
        for v in &vs {
            sizes += self.size(v);
        }
        self.charge(pos, sizes)?;
        let mut vs = vs;
        if matches!(builtin, Prelude::Resize | Prelude::Reinterpret) && vs.len() == 2 {
            return self.convert_call(pos, g, builtin, vs);
        }
        if builtin == Prelude::ListFn && vs.len() == 1 {
            let Some(t) = vs.pop() else {
                return fail(Code::S010, pos, format!("`{g}` needs one argument"));
            };
            return self.list_new(pos, g, &t);
        }
        if builtin == Prelude::Str && vs.len() == 1 {
            let Some(v) = vs.pop() else {
                return fail(Code::S010, pos, format!("`{g}` needs one argument"));
            };
            let v = self.data(pos, v)?;
            return self.str_of(pos, g, v);
        }
        self.refuse(pos, g, builtin, &vs)
    }

    /// `resize` or `reinterpret` of a value to a type, at the call `pos`. The arguments paid
    /// their copies.
    fn convert_call(
        &mut self,
        pos: Pos,
        g: &str,
        builtin: Prelude,
        mut vs: Vec<Out>,
    ) -> Res<Option<Out>> {
        let (Some(v), Some(t)) = (vs.pop(), vs.pop()) else {
            return fail(Code::S010, pos, format!("`{g}` needs two arguments"));
        };
        self.check_static(pos, &t)?;
        let Value::Type(ty) = self.store.value(&t) else {
            return fail(
                Code::S010,
                pos,
                format!(
                    "`{g}` needs a type, not {}",
                    self.store.value(&t).text(&self.tys)
                ),
            );
        };
        let ty = *ty;
        match self.data(pos, v)? {
            Opnd::Static(v) => {
                let v = self.store.value(&v);
                let made = if builtin == Prelude::Resize {
                    ops::resize(ty, v, &mut self.fuel, &self.tys)
                } else {
                    ops::reinterpret(ty, v, &mut self.fuel, &self.tys)
                };
                Ok(Some(Out::Made(Val::Static(made.map_err(at(pos))?))))
            }
            Opnd::Hw(x) => Ok(Some(Out::Made(self.hw_convert(pos, builtin, ty, x)?))),
        }
    }

    /// `static_assert` and `error` at the call `pos`, and the arguments that no prelude
    /// function accepts. The arguments paid their copies.
    fn refuse(&mut self, pos: Pos, g: &str, builtin: Prelude, vs: &[Out]) -> Res<Option<Out>> {
        match (builtin, vs) {
            (Prelude::StaticAssert, [c, m]) => {
                self.check_static(pos, c)?;
                self.check_static(pos, m)?;
                match (self.store.value(c), self.store.value(m)) {
                    (Value::Bool(true), Value::Str(_)) => Ok(None),
                    (Value::Bool(false), Value::Str(m)) => fail(
                        Code::S014,
                        pos,
                        format!("static assertion failed: {}", str_text(m)),
                    ),
                    (c, m) => fail(
                        Code::S010,
                        pos,
                        format!(
                            "`{g}` does not accept [{}, {}]",
                            c.text(&self.tys),
                            m.text(&self.tys)
                        ),
                    ),
                }
            }
            (Prelude::Error, [m]) => {
                self.check_static(pos, m)?;
                match self.store.value(m) {
                    Value::Str(m) => fail(Code::S014, pos, format!("error: {}", str_text(m))),
                    m => fail(
                        Code::S010,
                        pos,
                        format!("`{g}` does not accept {}", m.text(&self.tys)),
                    ),
                }
            }
            (_, vs) => {
                let texts: Vec<String> = vs.iter().map(|v| self.text(self.store.seen(v))).collect();
                fail(
                    Code::S010,
                    pos,
                    format!("`{g}` does not accept [{}]", texts.join(", ")),
                )
            }
        }
    }
}
