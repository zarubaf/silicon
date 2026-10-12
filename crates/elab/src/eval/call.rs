// SPDX-License-Identifier: Apache-2.0
//! The calls of Lean `Source.Eval`: a function item, a prelude function, and a type
//! constructor. A call charges its callee name, evaluates its arguments, and binds them in a
//! new call frame.

use super::{Evaluator, Opnd, Out, Res, Slot, Tag, at, fail};
use crate::Code;
use crate::hw::Val;
use crate::names::{Role, Step};
use crate::ops::{self, str_text};
use crate::value::Value;
use parse::ast::{Expr, Item, NodeId, Param, ParamMode, Pos};
use resolve::{DeclId, Kind, Prelude, Target};

impl Evaluator<'_> {
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
            match self.target(*fid) {
                Some(Target::Decl(id))
                    if matches!(self.file.decl(id).kind, Kind::Fn | Kind::Module) =>
                {
                    return self.call_fn(pos, node, *fp, g, id, xs);
                }
                Some(Target::Prelude(h)) if !h.is_type() => {
                    return self.call_prelude(pos, *fp, g, h, xs);
                }
                _ => {}
            }
        }
        self.construct(pos, f, xs)
    }

    /// A call of a function item. It runs in the call frame `<fn>$<k>c`. A hardware argument
    /// and a hardware result get a core name in that frame.
    fn call_fn(
        &mut self,
        pos: Pos,
        node: NodeId,
        fp: Pos,
        g: &str,
        id: DeclId,
        xs: &[Expr],
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
        let vs = self.args(xs)?;
        if params.len() != vs.len() {
            return fail(
                Code::S007,
                pos,
                format!(
                    "`{g}` takes {} argument(s), but it has {}",
                    params.len(),
                    vs.len()
                ),
            );
        }
        // A call outside a body runs on static values only, so its site never names hardware.
        let site = self
            .syms
            .calls
            .get(self.item)
            .and_then(|m| m.get(&node))
            .copied()
            .unwrap_or(0);
        let u = self.syms.items.get(i).copied().unwrap_or(0);
        self.nested(pos, |ev| {
            ev.in_frame(None, |ev| {
                let (path, frame) = ev.frame_of(u, Step::Call(site));
                ev.in_item(i, frame, |ev| {
                    for (q, v) in params.iter().zip(vs) {
                        ev.param(pos, *comptime, q, v)?;
                    }
                    let rt = ev.type_expr(ret)?;
                    ev.ret = Some(rt);
                    match ev.block(*ip, body, false)? {
                        Some(Val::Hw(h)) => {
                            let role = ev.paths.push(path, Step::Role(Role::Ret));
                            let name = ev.version(Tag::Ret, role);
                            Ok(Some(Out::Made(ev.bind_hw(pos, name, h))))
                        }
                        Some(v) => Ok(Some(Out::Made(v))),
                        None => fail(
                            Code::S010,
                            pos,
                            format!("`{}` ends without `return`", fn_name.name),
                        ),
                    }
                })
            })
        })
    }

    /// Binds a parameter of a call. Its type can use the parameters before it. A static
    /// parameter needs a static argument.
    fn param(&mut self, pos: Pos, comptime: bool, q: &Param, v: Out) -> Res<()> {
        let t = self.type_expr(&q.ty)?;
        self.charge(pos, self.size(&v))?;
        // TODO(#179): bind a `mut` formal to its place (plan step 28).
        if q.mode == ParamMode::Mut {
            return fail(
                Code::S010,
                pos,
                format!("the `mut` formal `{}` is not supported yet", q.name.name),
            );
        }
        let x = if comptime || q.mode == ParamMode::Comptime {
            let v = self.settle(pos, t, v)?;
            Val::Static(self.conform(pos, t, v)?)
        } else {
            self.conform_val(pos, t, v)?
        };
        let id = self.decl(&q.name)?;
        let x = self.named(pos, id, x);
        self.bind(
            id,
            Slot {
                ty: Some(t),
                mutable: false,
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
        xs: &[Expr],
    ) -> Res<Option<Out>> {
        self.charge(fp, 1)?;
        // TODO(#179): `list`, `push`, and `pop` (plan step 27).
        if matches!(builtin, Prelude::ListFn | Prelude::Push | Prelude::Pop) {
            return fail(Code::S010, pos, format!("`{g}` is not supported yet"));
        }
        let vs = self.args(xs)?;
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
            return match self.data(pos, v)? {
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
            };
        }
        if builtin == Prelude::Str && vs.len() == 1 {
            let Some(v) = vs.pop() else {
                return fail(Code::S010, pos, format!("`{g}` needs one argument"));
            };
            let v = self.data(pos, v)?;
            return self.str_of(pos, g, v);
        }
        match (builtin, vs.as_slice()) {
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
