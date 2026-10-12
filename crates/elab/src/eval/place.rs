// SPDX-License-Identifier: Apache-2.0
//! The index, the selector `.N`, `len`, and the places of Lean `Source.Eval`. An index and a
//! selector refer to an element, so they charge no size and copy nothing: a binding of the
//! result is the copy. An assignment to a place updates the one element in the local, because
//! no other binding shares the container. A read and a place each walk their path once.

use super::{Evaluator, Frame, Opnd, Out, Res, expr_pos, fail, need, same_form};
use crate::Code;
use crate::hw::{Ref, Root, Seen, Val};
use crate::int::Int;
use crate::ops::int_text;
use crate::types::TyId;
use crate::value::Value;
use parse::ast::{Expr, Ident, Nat, Pos};
use resolve::{DeclId, Target};
use std::borrow::Cow;

/// A step of a place or a read after its root: an index at the position with its arguments,
/// a selector `.N` with the positions of its node and of its number literal, or a field `.f`.
#[derive(Clone, Copy)]
enum Sel<'a> {
    Index(Pos, &'a [Expr]),
    Select(Pos, Pos, &'a Nat),
    Field(Pos, &'a Ident),
}

impl Sel<'_> {
    /// The position of the node of the step, where the step charges.
    fn pos(&self) -> Pos {
        let (Sel::Index(q, _) | Sel::Select(q, ..) | Sel::Field(q, _)) = *self;
        q
    }
}

/// A step of a place whose index evaluated: an index at its node, with the position of its
/// index expression and the index, or a selector `.N` as in `Sel`.
enum Key<'a> {
    Index(Pos, Pos, Index),
    Select(Pos, Pos, &'a Nat),
    Field(Pos, &'a Ident),
}

/// What the walk along a place knows of the type of the part: its type, no type, or the type
/// of the element itself, which it finds at the end.
#[derive(Clone, Copy)]
enum Known {
    Ty(TyId),
    Absent,
    Element,
}

/// What the part of a place is, for the operations that change it in place.
#[derive(Clone, Copy)]
pub(super) enum Held {
    /// A list with its element type and its length.
    List {
        elem: TyId,
        len: usize,
    },
    Other,
}

/// The result of the walk along a place.
struct Walked {
    keys: Vec<usize>,
    ty: Option<TyId>,
    in_list: bool,
    held: Held,
}

/// A place after its steps (section 5.2): its root, the number of each step, and the type and
/// the kind of the part. `in_list` tells if the container of the last step is a list.
pub(super) struct Place {
    pub(super) root: Root,
    pub(super) id: DeclId,
    pub(super) keys: Vec<usize>,
    pub(super) ty: Option<TyId>,
    pub(super) in_list: bool,
    pub(super) held: Held,
}

/// A static index, read once when it evaluates: its number, the text of an integer that no
/// `usize` holds, or the message of a value that is not an integer. A step checks it later
/// without the value of the index.
pub(super) enum Index {
    Number(usize),
    Wide(String),
    Bad(String),
}

/// An index of a type, which is complete: `S007` at the index.
fn fail_type_index<T>(q: Pos) -> Res<T> {
    fail(Code::S007, q, "a complete type takes no index".to_owned())
}

/// The root of a place and its steps from the root outward. Another target has no place.
fn chain(e: &Expr) -> Option<(&Expr, Vec<Sel<'_>>)> {
    let mut steps = Vec::new();
    let mut cur = e;
    loop {
        match cur {
            Expr::Index { pos, base, args } => {
                steps.push(Sel::Index(*pos, args));
                cur = base;
            }
            Expr::Select {
                pos,
                base,
                lit_pos,
                index,
            } => {
                steps.push(Sel::Select(*pos, *lit_pos, index));
                cur = base;
            }
            Expr::Field { pos, base, field } => {
                steps.push(Sel::Field(*pos, field));
                cur = base;
            }
            Expr::Name { .. } => {
                steps.reverse();
                return Some((cur, steps));
            }
            _ => return None,
        }
    }
}

/// The element `k` of the container `b`, as a reference to it. An index or a selector refers
/// to an element, so a binding of the result is a copy.
pub(super) fn elem(b: Opnd, k: usize) -> Out {
    match b {
        Opnd::Static(Out::Ref(Ref { root, mut path })) => {
            path.push(k);
            Out::Ref(Ref { root, path })
        }
        Opnd::Static(Out::Made(Val::Static(mut v)) | Out::Named(Val::Static(mut v))) => {
            Out::Named(Val::Static(take_element(&mut v, k)))
        }
        Opnd::Static(o) => o,
        Opnd::Hw(h) => Out::Made(Val::Hw(h)),
    }
}

/// The element `k` of an owned container.
fn take_element(v: &mut Value, k: usize) -> Value {
    match v {
        Value::Array(_, xs) | Value::Tuple(xs) | Value::Record(_, xs) | Value::List(_, xs) => xs
            .get_mut(k)
            .map_or(Value::Unit, |x| std::mem::replace(x, Value::Unit)),
        _ => Value::Unit,
    }
}

impl Evaluator<'_> {
    /// What an operand is.
    fn opnd_seen<'s>(&'s self, b: &'s Opnd) -> Seen<'s> {
        match b {
            Opnd::Static(o) => self.store.seen(o),
            Opnd::Hw(h) => Seen::Hw(*h),
        }
    }

    /// The static index `i`, read once. An index that is not an integer keeps its message.
    pub(super) fn index_of(&self, i: &Out) -> Index {
        let k = match self.store.value(i) {
            Value::Int(k) => Cow::Borrowed(k),
            Value::UInt(x) => Cow::Owned(Int::from_unsigned(x)),
            v => {
                return Index::Bad(format!(
                    "an index is a static integer, not {}",
                    v.text(&self.tys)
                ));
            }
        };
        match k.to_u64().and_then(|k| usize::try_from(k).ok()) {
            Some(k) => Index::Number(k),
            None => Index::Wide(int_text(&k)),
        }
    }

    /// The number of the element that the static index `i` at `q` picks from `base`, a result
    /// of an index at `pos`. The checks come in this order: the container (`S010`), the type
    /// of the index (`S010`), then its range (`S013`).
    pub(super) fn pick_at(&self, pos: Pos, q: Pos, base: Seen<'_>, i: &Index) -> Res<usize> {
        let len = match base {
            Seen::Static(Value::Array(_, xs) | Value::Tuple(xs) | Value::List(_, xs)) => xs.len(),
            s => {
                return fail(
                    Code::S010,
                    pos,
                    format!(
                        "an index needs an array, a list, or a tuple, not {}",
                        self.text(s)
                    ),
                );
            }
        };
        let range = |k: &str| {
            fail(
                Code::S013,
                q,
                format!("the index {k} is out of range for {len} element(s)"),
            )
        };
        match i {
            Index::Number(k) if *k < len => Ok(*k),
            Index::Number(k) => range(&k.to_string()),
            Index::Wide(k) => range(k),
            Index::Bad(m) => fail(Code::S010, q, m.clone()),
        }
    }

    /// The number of the element that the selector `.index` with its literal at `q` picks
    /// from `base`, a result of a selector at `pos`.
    fn select_at(&self, pos: Pos, q: Pos, index: &Nat, base: Seen<'_>) -> Res<usize> {
        let (len, v) = match base {
            Seen::Static(v @ Value::Tuple(xs)) => (xs.len(), v),
            s => {
                return fail(
                    Code::S010,
                    pos,
                    format!(
                        "the selector `.{}` needs a tuple, not {}",
                        selector_text(index),
                        self.text(s)
                    ),
                );
            }
        };
        match index.as_str().parse::<usize>() {
            Ok(k) if k < len => Ok(k),
            _ => fail(
                Code::S013,
                q,
                format!(
                    "the selector {} is out of range for {}",
                    selector_text(index),
                    v.text(&self.tys)
                ),
            ),
        }
    }

    /// The step of a read at `e` and its base: an index of a value, a selector `.N`, or a
    /// field `.f`. Another expression, also an index of a type, is the root of the read.
    fn read_step<'e>(&self, e: &'e Expr) -> Option<(Sel<'e>, &'e Expr)> {
        match e {
            Expr::Index { pos, base, args } => {
                let ty = match &**base {
                    Expr::Name { id, .. } => {
                        matches!(self.target(*id), Some(Target::Prelude(k)) if k.is_type())
                            || self.struct_item(*id).is_some()
                    }
                    _ => false,
                };
                (!ty).then_some((Sel::Index(*pos, args), &**base))
            }
            Expr::Select {
                pos,
                base,
                lit_pos,
                index,
            } => Some((Sel::Select(*pos, *lit_pos, index), &**base)),
            Expr::Field { pos, base, field } => Some((Sel::Field(*pos, field), &**base)),
            _ => None,
        }
    }

    /// A read `e` through indices, selectors `.N`, and fields `.f`, whose node charged. Each node charges
    /// before its base evaluates, from the outside in, and an index with more than one
    /// argument fails before its base. Then the root evaluates, and each step from the root
    /// outward reads its base as data and evaluates its index.
    ///
    /// Lean checks the container and the index of each step before the next index evaluates.
    /// Here the checks run in one walk along the path after the indices, so no step walks
    /// again from the root. A failed check comes before an error of a later index, so the
    /// first error is that of Lean. Only a static container has elements, so each base after
    /// the first is static data. A field of a root that is not static, for example a port of
    /// an instance, applies at once by the rule of `field`, before the walk.
    pub(super) fn read(&mut self, e: &Expr) -> Res<Option<Out>> {
        let mut steps = Vec::new();
        let mut next = self.read_step(e);
        let mut root = e;
        while let Some((step, base)) = next {
            if let Sel::Index(q, args) = step
                && args.len() != 1
            {
                return fail(
                    Code::S010,
                    q,
                    "an index of a value has one argument".to_owned(),
                );
            }
            steps.push(step);
            next = self.read_step(base);
            if next.is_some() {
                self.charge(expr_pos(base), 1)?;
            }
            root = base;
        }
        steps.reverse();
        let b = self.eval(root)?;
        let mut b = need(root, b)?;
        let mut done = 0;
        while let Some(Sel::Field(q, f)) = steps.get(done)
            && !matches!(self.store.seen(&b), Seen::Static(_))
        {
            b = self.field(*q, b, f)?;
            done += 1;
        }
        let steps = steps.split_off(done.min(steps.len()));
        let Some(first) = steps.first().map(Sel::pos) else {
            return Ok(Some(b));
        };
        let b = self.data(first, b)?;
        if let Some(Sel::Index(q, _)) = steps.first()
            && matches!(self.opnd_seen(&b), Seen::Static(Value::Type(_)))
        {
            return fail_type_index(*q);
        }
        if self.string_before_last(&b, &steps) {
            return self.read_exact(b, &steps);
        }
        let mut keyed = Vec::with_capacity(steps.len());
        let mut stop = None;
        // The base waits in the store, so that an index cannot change the value that it read.
        let at = self.store.park(b.into_out());
        for step in &steps {
            match self.key(step) {
                Ok(k) => keyed.push(k),
                Err(e) => {
                    stop = Some(e);
                    break;
                }
            }
        }
        let b = Opnd::of_out(self.store.resume_one(at));
        let (out, at_type) = self.follow(b, &keyed)?;
        if let Some(e) = stop {
            // The base of the step whose index failed is a type: that check comes first.
            if let Some(Sel::Index(q, _)) = steps.get(keyed.len())
                && at_type
            {
                return fail_type_index(*q);
            }
            return Err(e);
        }
        Ok(Some(out))
    }

    /// The walk of a read along the evaluated indices `keyed`, in one pass: the result, and
    /// whether the container after the last step is a type. A string container ends a segment:
    /// its index makes a new string, which is the base of the next segment.
    fn follow(&mut self, base: Opnd, keyed: &[Key<'_>]) -> Res<(Out, bool)> {
        let mut base = base;
        let mut rest = keyed;
        loop {
            let mut cur = self.opnd_seen(&base);
            let mut numbers = Vec::with_capacity(rest.len());
            let mut string_step = None;
            for (at, key) in rest.iter().enumerate() {
                let number = match key {
                    Key::Index(q, ..) if matches!(cur, Seen::Static(Value::Type(_))) => {
                        return fail_type_index(*q);
                    }
                    Key::Index(..) if matches!(cur, Seen::Static(Value::Str(_))) => {
                        string_step = Some(at);
                        break;
                    }
                    Key::Index(q, xp, i) => self.pick_at(*q, *xp, cur, i)?,
                    Key::Select(q, r, index) => self.select_at(*q, *r, index, cur)?,
                    Key::Field(q, f) => self.field_at(*q, f, cur)?.0,
                };
                cur = self.store.step(cur, number);
                numbers.push(number);
            }
            let at_type = matches!(cur, Seen::Static(Value::Type(_)));
            let mut path = numbers.into_iter();
            let mut out = match path.next() {
                Some(number) => elem(base, number),
                None => match base {
                    Opnd::Static(o) => o,
                    Opnd::Hw(h) => Out::Made(Val::Hw(h)),
                },
            };
            for number in path {
                out = elem(Opnd::Static(out), number);
            }
            let Some(at) = string_step else {
                return Ok((out, at_type));
            };
            let Some(Key::Index(q, xp, i)) = rest.get(at) else {
                return Ok((out, at_type));
            };
            base = Opnd::Static(self.str_at(*q, *xp, &out, i)?);
            rest = rest.get(at + 1..).unwrap_or_default();
        }
    }

    /// Whether a step of the read other than the last indexes a string, or might. Such a read
    /// runs its steps one by one (`read_exact`), because the scan of the string charges before
    /// the next index evaluates. Only the first index step of the path needs a look: its
    /// container holds a string if it is one, or if its element type holds one. The steps
    /// before it have fixed numbers.
    fn string_before_last(&self, base: &Opnd, steps: &[Sel<'_>]) -> bool {
        let mut cur = self.opnd_seen(base);
        for (n, step) in steps.iter().enumerate() {
            let k = match *step {
                Sel::Index(..) => {
                    return n + 1 < steps.len()
                        && match cur {
                            Seen::Static(Value::Str(_) | Value::Tuple(_)) => true,
                            Seen::Static(Value::Array(t, _) | Value::List(t, _)) => {
                                t.holds_string()
                            }
                            _ => false,
                        };
                }
                Sel::Select(q, r, index) => self.select_at(q, r, index, cur),
                Sel::Field(q, f) => self.field_at(q, f, cur).map(|(k, _)| k),
            };
            match k {
                Ok(k) => cur = self.store.step(cur, k),
                Err(_) => return false,
            }
        }
        false
    }

    /// A read whose steps run one by one, in the order of Lean `Source.Eval`: each step checks
    /// its container, evaluates its index, and then applies, before the next step starts. The
    /// result of a step refers to its container, so a step finds its container by the path from
    /// the root. The path is short where a string is on it, so the walk stays within a small
    /// factor of the steps.
    fn read_exact(&mut self, b: Opnd, steps: &[Sel<'_>]) -> Res<Option<Out>> {
        let mut cur = b;
        for step in steps {
            if let Sel::Index(q, _) = step
                && matches!(self.opnd_seen(&cur), Seen::Static(Value::Type(_)))
            {
                return fail_type_index(*q);
            }
            // The container waits in the store, so that the index cannot change its value.
            let at = self.store.park(cur.into_out());
            let key = self.key(step);
            cur = Opnd::of_out(self.store.resume_one(at));
            let key = key?;
            let out = match key {
                Key::Index(q, xp, i) => {
                    if let Opnd::Static(o) = &cur
                        && matches!(self.store.seen(o), Seen::Static(Value::Str(_)))
                    {
                        self.str_at(q, xp, o, &i)?
                    } else {
                        let k = self.pick_at(q, xp, self.opnd_seen(&cur), &i)?;
                        elem(cur, k)
                    }
                }
                Key::Select(q, r, index) => {
                    let k = self.select_at(q, r, index, self.opnd_seen(&cur))?;
                    elem(cur, k)
                }
                Key::Field(q, f) => {
                    let k = self.field_at(q, f, self.opnd_seen(&cur))?.0;
                    elem(cur, k)
                }
            };
            cur = Opnd::Static(out);
        }
        match cur {
            Opnd::Static(o) => Ok(Some(o)),
            Opnd::Hw(h) => Ok(Some(Out::Made(Val::Hw(h)))),
        }
    }

    /// `len` of an array, a list, or a string at the call `pos`. It refers to an array or a
    /// list, so it charges no size. A string needs a scan, so it charges its size first.
    pub(super) fn len(&mut self, pos: Pos, mut vs: Vec<Out>) -> Res<Option<Out>> {
        let (Some(v), true) = (vs.pop(), vs.is_empty()) else {
            return fail(
                Code::S007,
                pos,
                format!("`len` takes 1 argument(s), but it has {}", vs.len() + 1),
            );
        };
        let n = match self.data(pos, v)? {
            Opnd::Static(o) => match self.store.value(&o) {
                Value::Array(_, xs) | Value::List(_, xs) => xs.len() as u64,
                Value::Str(_) => {
                    let n = self.str_len(pos, &o)?;
                    return Ok(Some(Out::Made(Val::Static(n))));
                }
                v => {
                    return fail(
                        Code::S010,
                        pos,
                        format!(
                            "`len` takes an array, a list, or a string, not {}",
                            v.text(&self.tys)
                        ),
                    );
                }
            },
            Opnd::Hw(h) => {
                return fail(
                    Code::S010,
                    pos,
                    format!(
                        "`len` takes an array, not hardware {}",
                        self.tys.text_of(&self.graph.ty(h))
                    ),
                );
            }
        };
        Ok(Some(Out::Made(Val::Static(Value::Int(Int::from_u64(n))))))
    }

    /// An assignment to a `let mut` local, or to a part of it by indices, selectors `.N`, and
    /// fields. The place resolves first (`place_at`). Then the right side evaluates, with the
    /// type of the part as its type.
    pub(super) fn assign(&mut self, pos: Pos, target: &Expr, value: &Expr) -> Res<Option<Val>> {
        let place = self.place_at(pos, Code::S010, target)?;
        let o = self.eval(value)?;
        let o = need(value, o)?;
        self.copy(pos, &o)?;
        let y = if let Some(t) = place.ty {
            self.conform_val(pos, t, o)?
        } else {
            let old = self.store.current(place.root, &place.keys);
            let new = self.store.seen(&o);
            if !same_form(old, new) {
                return fail(
                    Code::S010,
                    pos,
                    format!(
                        "expected {}, but the value is {}",
                        self.text(old),
                        self.text(new)
                    ),
                );
            }
            self.store.take(o)
        };
        self.store_at(pos, expr_pos(value), &place, y)?;
        Ok(None)
    }

    /// The place `target` at `pos` (section 5.2). Its root is a `let mut` local, else the error
    /// is `code` at `pos`. The root name charges nothing. Each step charges 1 at its node, then
    /// its index evaluates, from the root outward.
    ///
    /// Lean checks the container and the index of each step before the next step charges.
    /// Here the checks run in one walk along the path after the indices, so no step walks
    /// again from the root. `S008` keeps the root unchanged while the indices evaluate, and
    /// a failed check comes before an error of a later step. Thus the first error is that of
    /// Lean.
    pub(super) fn place_at(&mut self, pos: Pos, code: Code, target: &Expr) -> Res<Place> {
        let bad = || {
            fail(
                code,
                pos,
                "the root of a place is a `let mut` local".to_owned(),
            )
        };
        let Some((Expr::Name { id: root_id, .. }, steps)) = chain(target) else {
            return bad();
        };
        let found = match self.target(*root_id) {
            Some(Target::Decl(id)) => self
                .store
                .frame()
                .and_then(|f: &Frame| f.get(&id))
                .filter(|s| s.mutable)
                .map(|s| (id, s.ty)),
            _ => None,
        };
        let Some((id, slot_ty)) = found else {
            return bad();
        };
        let frame = self.store.frames.len().saturating_sub(1);
        let root = Root::Local(frame, id);
        let mut keyed = Vec::with_capacity(steps.len());
        let mut stop = None;
        for step in &steps {
            match self.charge(step.pos(), 1).and_then(|()| self.key(step)) {
                Ok(k) => keyed.push(k),
                Err(e) => {
                    stop = Some(e);
                    break;
                }
            }
        }
        let walked = self.walk(root, slot_ty, &keyed)?;
        if let Some(e) = stop {
            return Err(e);
        }
        Ok(Place {
            root,
            id,
            keys: walked.keys,
            ty: walked.ty,
            in_list: walked.in_list,
            held: walked.held,
        })
    }

    /// A mutation at `pos` of a binding of the current frame (section 9.4). The binding is older
    /// than the innermost hardware arm when that arm started at the current depth: `S016`.
    pub(super) fn mutation(&self, pos: Pos) -> Res<()> {
        if self.arm == Some(self.depth) {
            return fail(
                Code::S016,
                pos,
                "a hardware arm changes a binding from before the arm".to_owned(),
            );
        }
        Ok(())
    }

    /// Writes `y` into the place (section 5.2). A place without a step binds its root again, so
    /// a hardware value gets the next version of the root. A step writes into the live value
    /// of the root. A list holds no hardware value: `S011` at `q`, the node of the value. A
    /// container holds no hardware value in this phase: `S010`.
    pub(super) fn store_at(&mut self, pos: Pos, q: Pos, place: &Place, y: Val) -> Res<()> {
        if place.keys.is_empty() {
            let y = self.named(pos, place.id, y);
            self.charge_held(pos, place.root)?;
            self.store.settle_root(place.root);
            if let Root::Local(frame, id) = place.root
                && let Some(slot) = self
                    .store
                    .frames
                    .get_mut(frame)
                    .and_then(|f| f.get_mut(&id))
            {
                slot.value = y;
            }
            return Ok(());
        }
        if place.in_list && matches!(y, Val::Hw(_)) {
            return fail(Code::S011, q, "a list holds no hardware value".to_owned());
        }
        let w = self.item(q, y)?;
        self.charge_held(pos, place.root)?;
        if let Some(part) = self.store.part_mut(place.root, &place.keys) {
            *part = w;
        }
        Ok(())
    }

    /// The step `step` of a place or a read with its index, which gets its static check.
    fn key<'a>(&mut self, step: &Sel<'a>) -> Res<Key<'a>> {
        match *step {
            Sel::Index(q, args) => {
                let [i] = args else {
                    return fail(
                        Code::S010,
                        q,
                        "an index of a value has one argument".to_owned(),
                    );
                };
                let o = self.eval(i)?;
                let o = need(i, o)?;
                let xp = expr_pos(i);
                self.check_static(xp, &o)?;
                Ok(Key::Index(q, xp, self.index_of(&o)))
            }
            Sel::Select(q, r, index) => Ok(Key::Select(q, r, index)),
            Sel::Field(q, f) => Ok(Key::Field(q, f)),
        }
    }

    /// The numbers of the steps `keyed` of the local at `root`, and the type of the part, in
    /// one walk from the root outward. `ty` is the type of the local, if it has one.
    ///
    /// Lean takes the part of the type at each step, and the type of the element when it has
    /// no type. The type of a tuple is the tuple of the types of its elements, so below a
    /// step without a type the type stays that of the element until an array gives its
    /// element type. Thus the walk finds the type of a tuple element only once, at the end,
    /// and not at each step.
    fn walk(&mut self, root: Root, ty: Option<TyId>, keyed: &[Key<'_>]) -> Res<Walked> {
        let mut keys = Vec::with_capacity(keyed.len());
        let mut cur = self.store.current(root, &[]);
        let mut in_list = false;
        let mut known = match ty {
            Some(t) => Known::Ty(t),
            None => Known::Absent,
        };
        for key in keyed {
            let (k, field) = match key {
                Key::Index(q, xp, i) => (self.pick_at(*q, *xp, cur, i)?, None),
                Key::Select(q, r, index) => (self.select_at(*q, *r, index, cur)?, None),
                Key::Field(q, f) => {
                    let (k, ft) = self.field_at(*q, f, cur)?;
                    (k, Some(ft))
                }
            };
            known = match (field, known, cur) {
                (Some(ft), _, _) => Known::Ty(ft),
                (None, Known::Ty(t), _) => self.tys.part(t, k).map_or(Known::Absent, Known::Ty),
                (
                    None,
                    Known::Element,
                    Seen::Static(Value::Array(elem, _) | Value::List(elem, _)),
                ) => Known::Ty(*elem),
                (None, Known::Absent | Known::Element, _) => Known::Element,
            };
            in_list = matches!(cur, Seen::Static(Value::List(..)));
            cur = self.store.step(cur, k);
            keys.push(k);
        }
        let held = match cur {
            Seen::Static(Value::List(elem, xs)) => Held::List {
                elem: *elem,
                len: xs.len(),
            },
            _ => Held::Other,
        };
        let ty = match known {
            Known::Ty(t) => Some(t),
            Known::Absent => None,
            Known::Element => cur.ty(&self.graph, &mut self.tys),
        };
        Ok(Walked {
            keys,
            ty,
            in_list,
            held,
        })
    }

    /// The value of an element of a container in this phase. A hardware value is `S010`,
    /// and so is a handle until slice 3.
    fn item(&self, pos: Pos, v: Val) -> Res<Value> {
        match v {
            Val::Static(v) => Ok(v),
            Val::Hw(_) => fail(
                Code::S010,
                pos,
                "a container holds only static values in this phase".to_owned(),
            ),
            Val::Handle(h) => {
                let v = Val::Handle(h);
                fail(
                    Code::S010,
                    pos,
                    format!("{} is not an element before slice 3", self.text(v.seen())),
                )
            }
            Val::Pending(q, _) => super::no_type(q),
        }
    }
}

/// A selector in a message, with at most 256 bits of a large number.
fn selector_text(index: &Nat) -> String {
    Int::from_decimal(index.as_str()).map_or_else(|| index.as_str().to_owned(), |n| int_text(&n))
}
