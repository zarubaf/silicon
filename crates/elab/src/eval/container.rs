// SPDX-License-Identifier: Apache-2.0
//! The containers of Lean `Source.Eval`: the tuple and array literals, the literals that wait
//! for the type of a typed use, and the new containers with their depth bound. An element is a
//! static value, a hardware value, or a hardware aggregate (section 5.1).
//!
//! A new container checks its depth, then pays the charge of its size, and only then copies
//! its elements. The elements stay borrowed until then, so a reference to a large value costs
//! nothing before the charge. The size, the depth, and the number of hardware leaves of an
//! element come from its stored numbers.

use super::{Evaluator, Out, Res, Store, at, fail, need};
use crate::Code;
use crate::agg::Agg;
use crate::hw::{Graph, Part, Seen, Val};
use crate::int::Int;
use crate::ops::{self, Fuel};
use crate::types::{Ty, TyId, Types};
use crate::value::Value;
use parse::ast::{Expr, Pos};
use std::borrow::Cow;
use std::cmp::Ordering;

/// What the construction of a container reads: the store that its references name, and the
/// nesting depth.
#[derive(Clone, Copy)]
struct Env<'x> {
    store: &'x Store,
    limit: u64,
    site: Option<Pos>,
}

/// A new value or type of the depth `depth` at `pos`. Above the nesting depth, it is `S015`
/// at `pos`, or at the name `site` of a function value whose signature evaluates.
pub(super) fn bounded(limit: u64, site: Option<Pos>, pos: Pos, depth: u64) -> Res<()> {
    if limit < depth {
        return fail(
            Code::S015,
            site.unwrap_or(pos),
            format!(
                "the depth {depth} goes above the nesting depth {limit}; raise --depth to at least {depth}"
            ),
        );
    }
    Ok(())
}

/// The static value of a result that is an element of a container.
fn cow(store: &Store, out: Out) -> Cow<'_, Value> {
    match out {
        Out::Made(Val::Static(v)) | Out::Named(Val::Static(v)) | Out::Kept(Val::Static(v), _) => {
            Cow::Owned(v)
        }
        Out::Ref(r) => Cow::Borrowed(store.value_at(&r)),
        Out::Made(_) | Out::Named(_) | Out::Kept(..) => Cow::Owned(Value::Unit),
    }
}

/// A tuple literal at `pos`: its depth, then the charge of its size.
fn tuple_of(env: Env<'_>, fuel: &mut Fuel, pos: Pos, elems: Vec<Cow<'_, Value>>) -> Res<Value> {
    let depth = 1 + elems.iter().map(|e| e.depth()).max().unwrap_or(0);
    bounded(env.limit, env.site, pos, depth)?;
    let size = 1 + elems.iter().map(|e| u128::from(e.size())).sum::<u128>();
    fuel.pay(size).map_err(at(pos))?;
    Ok(Value::tuple(
        elems.into_iter().map(Cow::into_owned).collect(),
    ))
}

/// An array literal at `pos`. Its elements take their common type. Then it checks its depth
/// and charges its size.
fn array_of<'x>(
    env: Env<'x>,
    fuel: &mut Fuel,
    tys: &mut Types,
    pos: Pos,
    elems: Vec<Cow<'x, Value>>,
) -> Res<Value> {
    let (units, common) = ops::common_of(
        elems.iter().map(|e| &**e),
        |v, tys| v.ty(tys),
        tys,
        fuel.left(),
    );
    fuel.pay_joins(&units).map_err(at(pos))?;
    let Some(t) = common else {
        return fail(
            Code::S010,
            pos,
            "the elements of an array have no common type".to_owned(),
        );
    };
    let mut xs = Vec::with_capacity(elems.len());
    for e in elems {
        xs.push(match ops::convert(t, &e, fuel, tys).map_err(at(pos))? {
            Some(v) => Cow::Owned(v),
            None => e,
        });
    }
    let depth = 1 + xs.iter().map(|x| x.depth()).fold(t.depth(), u64::max);
    bounded(env.limit, env.site, pos, depth)?;
    let size = 1 + xs.iter().map(|x| u128::from(x.size())).sum::<u128>();
    fuel.pay(size).map_err(at(pos))?;
    Ok(Value::Array(
        t,
        xs.into_iter().map(Cow::into_owned).collect(),
    ))
}

fn mismatch<T>(pos: Pos, t: TyId, what: &str, tys: &Types) -> Res<T> {
    fail(
        Code::S010,
        pos,
        format!("expected {}, but the value is {what}", tys.text(t)),
    )
}

/// An element of a container that is being built: a result in the store, a part of a literal
/// that waits, or a part that a typed use made.
pub(super) enum Piece<'x> {
    Out(Out),
    Part(&'x Agg),
    New(Agg),
}

/// What a piece is, without a copy.
fn piece_seen<'a>(store: &'a Store, p: &'a Piece<'_>) -> Seen<'a> {
    match p {
        Piece::Out(o) => store.seen(o),
        Piece::Part(a) => a.seen(),
        Piece::New(a) => a.seen(),
    }
}

/// The static value of a piece that is static.
fn cow_of<'a>(store: &'a Store, p: Piece<'a>) -> Cow<'a, Value> {
    match p {
        Piece::Out(o) => cow(store, o),
        Piece::Part(Agg::Static(v)) => Cow::Borrowed(v),
        Piece::New(Agg::Static(v)) => Cow::Owned(v),
        Piece::Part(_) | Piece::New(_) => Cow::Owned(Value::Unit),
    }
}

/// The size, the depth, and the number of hardware leaves of what a piece is, from its stored
/// numbers.
fn numbers(g: &Graph, tys: &Types, s: Seen<'_>) -> (u64, u64, u64) {
    match s {
        Seen::Static(v) => (v.size(), v.depth(), 0),
        Seen::Hw(h) => (g.size(h), 1, 1),
        Seen::Agg(a) => (a.size(g, tys), a.depth(tys), a.leaves(tys)),
        Seen::Handle(_) | Seen::Pending(..) => (1, 1, 0),
    }
}

impl<'x> Piece<'x> {
    /// The piece of a result that is an element.
    fn of_outs(outs: Vec<Out>) -> Vec<Piece<'x>> {
        outs.into_iter().map(Piece::Out).collect()
    }
}

impl Evaluator<'_> {
    /// Whether each piece is a static value.
    fn all_static(&self, pieces: &[Piece<'_>]) -> bool {
        pieces
            .iter()
            .all(|p| matches!(piece_seen(&self.store, p), Seen::Static(_)))
    }

    /// The type of a piece.
    fn piece_ty(&mut self, pos: Pos, p: &Piece<'_>) -> Res<TyId> {
        match piece_seen(&self.store, p).ty(&self.graph, &mut self.tys) {
            Some(t) => Ok(t),
            None => fail(Code::S010, pos, "an element has no type".to_owned()),
        }
    }

    /// The part that a piece gives. A result or a part that waits copies now: the caller paid
    /// the charge of the node that holds the part.
    fn part_of_piece(&self, p: Piece<'_>) -> Agg {
        match p {
            Piece::Out(o) => Agg::of_val(self.store.take(o)).unwrap_or(Agg::Static(Value::Unit)),
            Piece::Part(a) => a.clone(),
            Piece::New(a) => a,
        }
    }

    /// The typed use of the piece `p` at the type `t` at `pos` (Lean `conformAgg`). A static
    /// part converts, a hardware leaf needs the type `t`, and a hardware aggregate converts
    /// part by part (`typed_agg`). A part of the type `t` stays where it is.
    pub(super) fn conform_piece<'x>(&mut self, pos: Pos, t: TyId, p: Piece<'x>) -> Res<Piece<'x>> {
        enum Is {
            Static,
            Hw(crate::hw::HwId),
            Agg(bool),
            Other,
        }
        let is = match piece_seen(&self.store, &p) {
            Seen::Static(_) => Is::Static,
            Seen::Hw(h) => Is::Hw(h),
            Seen::Agg(a) => Is::Agg(a.stored_ty() == Some(t)),
            Seen::Handle(_) | Seen::Pending(..) => Is::Other,
        };
        match is {
            Is::Static => {
                let Seen::Static(v) = piece_seen(&self.store, &p) else {
                    return Ok(p);
                };
                match ops::convert(t, v, &mut self.fuel, &self.tys).map_err(at(pos))? {
                    Some(w) => Ok(Piece::New(Agg::Static(w))),
                    None => Ok(p),
                }
            }
            Is::Hw(h) => {
                let ty = self.graph.ty(h);
                if ty == *self.tys.get(t) {
                    Ok(p)
                } else {
                    fail(
                        Code::S010,
                        pos,
                        format!(
                            "expected {}, but the value is {}",
                            self.tys.text(t),
                            self.tys.text_of(&ty)
                        ),
                    )
                }
            }
            Is::Agg(true) => Ok(p),
            Is::Agg(false) => match p {
                Piece::Out(o) => Ok(Piece::New(self.typed_agg(pos, t, o)?)),
                Piece::Part(a) => Ok(Piece::New(self.typed_part(pos, t, a)?)),
                Piece::New(a) => Ok(Piece::New(self.typed_part(pos, t, &a)?)),
            },
            Is::Other => fail(
                Code::S010,
                pos,
                "an element of a container is data".to_owned(),
            ),
        }
    }

    /// The new container node of the type `ty` at `pos` with the pieces: its depth (`S015`),
    /// then the charge of its size from the stored numbers of the pieces. Only then do the pieces
    /// copy.
    pub(super) fn made_pieces(&mut self, pos: Pos, ty: TyId, pieces: Vec<Piece<'_>>) -> Res<Agg> {
        let parts = pieces
            .iter()
            .map(|p| numbers(&self.graph, &self.tys, piece_seen(&self.store, p)));
        let Some(node) = Agg::shape_from(&self.tys, ty, pieces.len(), parts) else {
            return fail(Code::S010, pos, "the part has the wrong shape".to_owned());
        };
        self.bounded(pos, node.depth)?;
        self.charge(pos, u128::from(node.size))?;
        let xs = pieces.into_iter().map(|p| self.part_of_piece(p)).collect();
        Ok(Agg::finish(&self.tys, node, xs))
    }

    /// A tuple literal at `pos` with the pieces. A tuple of static values keeps the charges of a
    /// static value. Another one has the type of its elements.
    pub(super) fn tuple_piece(&mut self, pos: Pos, pieces: Vec<Piece<'_>>) -> Res<Agg> {
        if self.all_static(&pieces) {
            let env = Env {
                store: &self.store,
                limit: self.limit,
                site: self.site,
            };
            let elems = pieces.into_iter().map(|p| cow_of(env.store, p)).collect();
            return tuple_of(env, &mut self.fuel, pos, elems).map(Agg::Static);
        }
        let mut types = Vec::with_capacity(pieces.len());
        for p in &pieces {
            types.push(self.piece_ty(pos, p)?);
        }
        let ty = self.tys.tuple(types);
        self.made_pieces(pos, ty, pieces)
    }

    /// An array literal at `pos` with the pieces. Its elements take their common type by a typed
    /// use. Then it checks its depth and charges its size.
    pub(super) fn array_piece(&mut self, pos: Pos, pieces: Vec<Piece<'_>>) -> Res<Agg> {
        if self.all_static(&pieces) {
            let env = Env {
                store: &self.store,
                limit: self.limit,
                site: self.site,
            };
            let elems = pieces.into_iter().map(|p| cow_of(env.store, p)).collect();
            return array_of(env, &mut self.fuel, &mut self.tys, pos, elems).map(Agg::Static);
        }
        let mut types = Vec::with_capacity(pieces.len());
        for p in &pieces {
            types.push(self.piece_ty(pos, p)?);
        }
        let (units, common) = ops::common_of(types, |t, _| *t, &mut self.tys, self.fuel.left());
        self.fuel.pay_joins(&units).map_err(at(pos))?;
        let Some(t) = common else {
            return fail(
                Code::S010,
                pos,
                "the elements of an array have no common type".to_owned(),
            );
        };
        let mut conformed = Vec::with_capacity(pieces.len());
        for p in pieces {
            conformed.push(self.conform_piece(pos, t, p)?);
        }
        let ty = self.tys.array(t, Int::from_u64(conformed.len() as u64));
        self.made_pieces(pos, ty, conformed)
    }

    /// A literal that waits, at a typed use of the type `t` at `pos`. The type flows into each
    /// element: `[]` takes the type `[T; 0]`, and a literal of the shape of `t` makes its
    /// elements at the element types of `t`. Then the literal charges as it does at its node.
    /// Another shape is `S010` at `pos`.
    fn build<'x>(&mut self, pos: Pos, ty: TyId, part: &'x Part) -> Res<Piece<'x>> {
        match part {
            Part::Value(a) => Ok(Piece::Part(a)),
            Part::Empty(node) => match self.tys.get(ty) {
                Ty::Array(elem, len) if len.cmp_u64(0) == Ordering::Equal => {
                    let empty = Value::Array(*elem, Vec::new());
                    self.bounded(*node, empty.depth())?;
                    Ok(Piece::New(Agg::Static(empty)))
                }
                _ => mismatch(pos, ty, "`[]`", &self.tys),
            },
            Part::Array(node, parts) => match self.tys.get(ty) {
                Ty::Array(elem, len) if len.cmp_u64(parts.len() as u64) == Ordering::Equal => {
                    let elem = *elem;
                    let mut pieces = Vec::with_capacity(parts.len());
                    for part in parts {
                        pieces.push(self.build(pos, elem, part)?);
                    }
                    self.array_piece(*node, pieces).map(Piece::New)
                }
                _ => mismatch(pos, ty, "an array literal with `[]`", &self.tys),
            },
            Part::Tuple(node, parts) => match self.tys.get(ty) {
                Ty::Tuple(types) if types.len() == parts.len() => {
                    let mut pieces = Vec::with_capacity(parts.len());
                    for (k, part) in parts.iter().enumerate() {
                        let elem_ty = self.tys.part(ty, k).unwrap_or(ty);
                        pieces.push(self.build(pos, elem_ty, part)?);
                    }
                    self.tuple_piece(*node, pieces).map(Piece::New)
                }
                _ => mismatch(pos, ty, "a tuple literal with `[]`", &self.tys),
            },
        }
    }

    /// A new value or type of the depth `depth` at `pos`.
    pub(super) fn bounded(&self, pos: Pos, depth: u64) -> Res<()> {
        bounded(self.limit, self.site, pos, depth)
    }

    /// Checks that `o` can be an element of a container at `pos`. A static value, a hardware
    /// value, and a hardware aggregate can. A handle is `S010` until slice 3. A literal that
    /// waits for its type gives the position of its first `[]`.
    pub(super) fn held(&self, pos: Pos, o: &Out) -> Res<Option<Pos>> {
        match self.store.seen(o) {
            Seen::Static(_) | Seen::Hw(_) | Seen::Agg(_) => Ok(None),
            Seen::Pending(q, _) => Ok(Some(q)),
            s @ Seen::Handle(_) => fail(
                Code::S010,
                pos,
                format!("{} is not an element before slice 3", self.text(s)),
            ),
        }
    }

    /// The elements of a container literal, each checked as it evaluates. The position is that
    /// of the first `[]` among the elements that wait.
    pub(super) fn elements(&mut self, xs: &[Expr]) -> Res<(Vec<Out>, Option<Pos>)> {
        let base = self.store.parked.len();
        let mut waiting = None;
        for x in xs {
            let o = self.eval(x)?;
            let o = need(x, o)?;
            if let Some(q) = self.held(super::expr_pos(x), &o)? {
                waiting.get_or_insert(q);
            }
            self.store.park(o);
        }
        Ok((self.store.resume(base), waiting))
    }

    /// A container expression: `()`, a tuple or an array literal, or a selector `.N`. A literal
    /// with `[]` waits for the type of a typed use.
    pub(super) fn container(&mut self, e: &Expr) -> Res<Option<Out>> {
        match e {
            Expr::Unit { pos } => self.made(*pos, Value::Unit),
            Expr::Tuple { pos, elems } => {
                let (outs, waiting) = self.elements(elems)?;
                if let Some(q) = waiting {
                    let parts = outs.into_iter().map(|o| self.store.part(o)).collect();
                    return Ok(Some(Out::Made(Val::Pending(q, Part::Tuple(*pos, parts)))));
                }
                let a = self.tuple_piece(*pos, Piece::of_outs(outs))?;
                Ok(Some(Out::Made(a.into_val())))
            }
            Expr::Array { pos, elems } if elems.is_empty() => {
                self.charge(*pos, 1)?;
                Ok(Some(Out::Made(Val::Pending(*pos, Part::Empty(*pos)))))
            }
            Expr::Array { pos, elems } => {
                let (outs, waiting) = self.elements(elems)?;
                if let Some(q) = waiting {
                    let parts = outs.into_iter().map(|o| self.store.part(o)).collect();
                    return Ok(Some(Out::Made(Val::Pending(q, Part::Array(*pos, parts)))));
                }
                let a = self.array_piece(*pos, Piece::of_outs(outs))?;
                Ok(Some(Out::Made(a.into_val())))
            }
            _ => fail(
                Code::S010,
                super::expr_pos(e),
                "not a container expression".to_owned(),
            ),
        }
    }

    /// A typed use of the type `t` at `pos` gives a literal that waits its type.
    pub(super) fn settle(&mut self, pos: Pos, t: TyId, out: Out) -> Res<Out> {
        let Out::Made(Val::Pending(_, part)) = out else {
            return Ok(out);
        };
        let piece = self.build(pos, t, &part)?;
        Ok(Out::Made(self.part_of_piece(piece).into_val()))
    }
}
