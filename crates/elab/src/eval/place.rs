// SPDX-License-Identifier: Apache-2.0
//! The index, the selector `.N`, `len`, and the places of Lean `Source.Eval`. An index and a
//! selector refer to an element, so they charge no size and copy nothing: a binding of the
//! result is the copy. An assignment to a place updates the one element in the local, because
//! no other binding shares the container. A read and a place each walk their path once.

use super::field::{At, InstInfo};
use super::handle::same_form;
use super::store::Mark;
use super::typed::Whole;
use super::{Evaluator, Opnd, Out, Res, fail, need};
use crate::Code;
use crate::agg::Agg;
use crate::hw::{Handle, Kind as Resource, Ref, Root, Seen, Val};
use crate::int::Int;
use crate::names::Step;
use crate::ops::{int_text, str_text};
use crate::types::{Ty, TyId};
use crate::value::Value;
use parse::ast::{Builtin, Expr, Ident, Nat, Pos};
use resolve::{DeclId, Target};
use std::borrow::Cow;

/// A step of a place or a read after its root: an index at the position with its arguments,
/// a selector `.N` with the positions of its node and of its number literal, a field `.f`, or an
/// `@field` selection with its base and its key. The key of an `@field` is an index with a call
/// for the scan (`CallArgs`), which marks the address of the key.
#[derive(Clone, Copy)]
pub(super) enum Sel<'a> {
    Index(Pos, &'a [Expr]),
    Select(Pos, Pos, &'a Nat),
    Field(Pos, &'a Ident),
    Key(Pos, &'a Expr, &'a Expr),
}

impl Sel<'_> {
    /// The position of the node of the step, where the step charges.
    pub(super) fn pos(&self) -> Pos {
        let (Sel::Index(q, _) | Sel::Select(q, ..) | Sel::Field(q, _) | Sel::Key(q, ..)) = *self;
        q
    }
}

/// A step of a place whose index evaluated: an index at its node, with the position of its
/// index expression and the index, or a selector `.N` as in `Sel`. The key of an `@field` step
/// waits as a static result, because its kind checks need the base (`Named`).
pub(super) enum Key<'a> {
    Index(Pos, Pos, Index),
    Select(Pos, Pos, &'a Nat),
    Field(Pos, &'a Ident),
    Named(Named<'a>),
}

/// An `@field` step at `pos` after its key evaluated and passed the static check. The base is the
/// expression of the first operand, for the position of an error and for the text of a family.
/// The key is the static result at `kp`. `at` is its number if it is a non-negative integer, so
/// the cursor of a read names the part before the base is known.
pub(super) struct Named<'a> {
    pub(super) pos: Pos,
    pub(super) base: &'a Expr,
    pub(super) kp: Pos,
    pub(super) key: Out,
    pub(super) at: Option<usize>,
    /// The key is a `String` or a `PortKey`: its name charges its size.
    pub(super) charges: bool,
    /// The size of the name of the key is paid already. A read pays it at the step when the base
    /// reads nothing, as Lean charges it before the next key evaluates, and a query pays it at
    /// its step.
    pub(super) paid: bool,
}

/// The result of the walk of a read (`follow`).
pub(super) struct Followed {
    pub(super) out: Out,
    /// The container after the last step is a type.
    at_type: bool,
    /// The last step is the index of a string.
    string_last: bool,
}

impl Opnd {
    /// The local that an index of this base can change while its own index evaluates: the local
    /// of a reference, or of a copy that still holds its local.
    fn changing_root(&self) -> Option<Root> {
        match self {
            Opnd::Static(Out::Ref(r)) if matches!(r.root, Root::Local(..)) => Some(r.root),
            Opnd::Static(o) => o.kept(),
            Opnd::Hw(_) => None,
        }
    }
}

impl Followed {
    fn new(out: Out, at_type: bool, string_last: bool) -> Followed {
        Followed {
            out,
            at_type,
            string_last,
        }
    }
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

/// The size and the number of hardware leaves of the part of a place in an aggregate root. They
/// come from the stored numbers of the part, so the rebind charge needs no walk of a node.
#[derive(Clone, Copy)]
pub(super) struct PartInfo {
    pub(super) size: u64,
    pub(super) leaves: u64,
}

/// The result of the walk along a place.
struct Walked {
    keys: Vec<usize>,
    /// What the walk knows of the type, for the next group of steps.
    known: Known,
    ty: Option<TyId>,
    in_list: bool,
    held: Held,
    part: Option<PartInfo>,
    own: Option<Val>,
    /// The walk ended inside a static value of the root, which holds no reference: no later step
    /// normalizes a part, so the next steps need no catch-up.
    settled: bool,
}

/// The steps of a read or a place whose keys evaluated and that no walk took yet, in their order.
/// `waiting` holds the numbers of the steps whose `@field` key refers to a `let mut` local, or to
/// a part of one (`push_key`): a later key with a call can change the local before the walk.
/// `within` holds the type of the container of each step, if it is known, and the first `checked`
/// steps passed their checks by that type (`Evaluator::checked`).
struct Keyed<'a> {
    keys: Vec<Key<'a>>,
    waiting: Vec<usize>,
    within: Vec<Option<TyId>>,
    checked: usize,
}

impl<'a> Keyed<'a> {
    fn new(capacity: usize) -> Self {
        Keyed {
            keys: Vec::with_capacity(capacity),
            waiting: Vec::new(),
            within: Vec::with_capacity(capacity),
            checked: 0,
        }
    }

    fn keys(&self) -> &[Key<'a>] {
        &self.keys
    }

    /// The walk took the steps, so none waits.
    fn clear(&mut self) {
        self.keys.clear();
        self.waiting.clear();
        self.within.clear();
        self.checked = 0;
    }
}

/// Where the walk along a place is: a view of a value in the store, or a value that the walk
/// made. A step into a reference makes a new reference, which no path names, and so do the
/// steps below it.
enum Cur<'s> {
    In(Seen<'s>),
    Own(Val),
}

impl Walked {
    /// The start of a walk from the root of a local with the type `ty`, if it has one.
    fn start(ty: Option<TyId>) -> Self {
        Walked {
            keys: Vec::new(),
            known: ty.map_or(Known::Absent, Known::Ty),
            ty,
            in_list: false,
            held: Held::Other,
            part: None,
            own: None,
            settled: false,
        }
    }
}

impl Cur<'_> {
    /// The value that the walk made, if the part is not in the store.
    fn into_own(self) -> Option<Val> {
        match self {
            Cur::Own(v) => Some(v),
            Cur::In(_) => None,
        }
    }

    fn seen(&self) -> Seen<'_> {
        match self {
            Cur::In(s) => *s,
            Cur::Own(v) => v.seen(),
        }
    }
}

/// The position of the node of a step.
pub(super) fn key_pos(key: &Key<'_>) -> Pos {
    match key {
        Key::Index(q, ..) | Key::Select(q, ..) | Key::Field(q, _) => *q,
        Key::Named(n) => n.pos,
    }
}

/// A place after its steps (section 5.2): its root, the number of each step, and the type and
/// the kind of the part. `in_list` tells if a step selects an element of a list. A place in an
/// aggregate root also holds the numbers of its part, and the part itself if it is a reference
/// that the walk made, for no path names it.
pub(super) struct Place {
    pub(super) root: Root,
    pub(super) id: DeclId,
    pub(super) keys: Vec<usize>,
    pub(super) ty: Option<TyId>,
    pub(super) in_list: bool,
    pub(super) held: Held,
    pub(super) part: Option<PartInfo>,
    pub(super) own: Option<Val>,
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
pub(super) fn chain(e: &Expr) -> Option<(&Expr, Vec<Sel<'_>>)> {
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
            Expr::Builtin {
                pos,
                builtin: Builtin::Field,
                args,
            } => {
                let [base, key] = args.as_slice() else {
                    return None;
                };
                steps.push(Sel::Key(*pos, base, key));
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
        Opnd::Static(Out::Kept(Val::Static(mut v), root)) => {
            Out::Kept(Val::Static(take_element(&mut v, k)), root)
        }
        Opnd::Static(o) => o,
        Opnd::Hw(h) => Out::Made(Val::Hw(h)),
    }
}

/// The element `k` of an owned container.
fn take_element(v: &mut Value, k: usize) -> Value {
    match v {
        Value::Array(_, xs) | Value::Tuple(_, xs) | Value::Record(_, xs) | Value::List(_, xs) => xs
            .get_mut(k)
            .map_or(Value::Unit, |x| std::mem::replace(x, Value::Unit)),
        _ => Value::Unit,
    }
}

impl Evaluator<'_> {
    /// What an operand is.
    pub(super) fn opnd_seen<'s>(&'s self, b: &'s Opnd) -> Seen<'s> {
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
            Seen::Static(Value::Array(_, xs) | Value::Tuple(_, xs) | Value::List(_, xs)) => {
                Some(xs.len() as u64)
            }
            Seen::Agg(a) => self.index_len(a),
            _ => None,
        };
        let Some(len) = len else {
            return fail(
                Code::S010,
                pos,
                format!(
                    "an index needs an array, a list, or a tuple, not {}",
                    self.text(base)
                ),
            );
        };
        Self::within(q, len, i)
    }

    /// The number of the part that the evaluated step `key` takes from `base`, after its checks,
    /// and the declared type of the part when the step names a field (Lean `placeStep`).
    pub(super) fn step_at(&self, key: &Key<'_>, base: Seen<'_>) -> Res<(usize, Option<TyId>)> {
        match key {
            Key::Index(q, xp, i) => Ok((self.pick_at(*q, *xp, base, i)?, None)),
            Key::Select(q, r, index) => Ok((self.select_at(*q, *r, index, base)?, None)),
            Key::Field(q, f) => {
                let (k, ft) = self.field_at(*q, f, base)?;
                Ok((k, Some(ft)))
            }
            // The caller paid the name of the step.
            Key::Named(n) => self.named_number(n, base),
        }
    }

    /// The number of the element that the selector `.index` with its literal at `q` picks
    /// from `base`, a result of a selector at `pos`.
    fn select_at(&self, pos: Pos, q: Pos, index: &Nat, base: Seen<'_>) -> Res<usize> {
        self.no_enum_field(pos, &selector_text(index), base)?;
        let len = match base {
            Seen::Static(Value::Tuple(_, xs)) => Some(xs.len()),
            Seen::Agg(a) => self.select_len(a),
            _ => None,
        };
        let Some(len) = len else {
            return fail(
                Code::S010,
                pos,
                format!(
                    "the selector `.{}` needs a tuple, not {}",
                    selector_text(index),
                    self.text(base)
                ),
            );
        };
        match index.as_str().parse::<usize>() {
            Ok(k) if k < len => Ok(k),
            _ => fail(
                Code::S013,
                q,
                format!(
                    "the selector {} is out of range for {}",
                    selector_text(index),
                    self.text(base)
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
                            || self.family_of(*id).is_some()
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
            Expr::Builtin {
                pos,
                builtin: Builtin::Field,
                args,
            } => match args.as_slice() {
                [base, key] => Some((Sel::Key(*pos, base, key), base)),
                _ => None,
            },
            _ => None,
        }
    }

    /// A read `e` through indices, selectors `.N`, and fields `.f`, whose node charged. Each node charges
    /// before its base evaluates, from the outside in, and an index with more than one
    /// argument fails before its base. Then the root evaluates, and each step from the root
    /// outward reads its base as data and evaluates its index.
    ///
    /// Lean checks the container and the index of each step before the next index evaluates.
    /// Here the checks of each segment (`segment`) run in one walk along the path after its
    /// indices, so no step walks again from the root. A failed check comes before an error of a
    /// later index, so the first error is that of Lean. A key with a call can make a record, so
    /// the steps before it pass their checks by their types first (`checked`), or the segment
    /// ends before it. Only a static container has elements, so each base after
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
                self.charge(base.pos(), 1)?;
            }
            root = base;
        }
        steps.reverse();
        let b = self.eval(root)?;
        let b = need(root, b)?;
        // The fields at the start take no index, so a stored root runs through its nodes at once.
        let fields: Vec<Key<'_>> = steps
            .iter()
            .map_while(|s| match *s {
                Sel::Field(q, f) => Some(Key::Field(q, f)),
                _ => None,
            })
            .collect();
        let (through, done) = self.node_steps(Opnd::of_out(b), &fields);
        let (b, done) = self.index_base(through.into_out(), &steps, done)?;
        let steps = steps.split_off(done.min(steps.len()));
        let Some(first) = steps.first().map(Sel::pos) else {
            return Ok(Some(b));
        };
        // The base of an `@field` reads after its key evaluates (Lean `fieldOut`).
        let b = match steps.first() {
            Some(Sel::Key(..)) => Opnd::of_out(b),
            _ => self.base_data(first, b)?,
        };
        if let Some(Sel::Index(q, _)) = steps.first()
            && matches!(self.opnd_seen(&b), Seen::Static(Value::Type(_)))
        {
            return fail_type_index(*q);
        }
        let mut known = self.base_ty(&b);
        let mut base = b;
        let mut rest: &[Sel<'_>] = &steps;
        loop {
            let (out, done, after) = self.segment(base, rest, known)?;
            rest = rest.get(done..).unwrap_or_default();
            if rest.is_empty() {
                return Ok(Some(out));
            }
            // The type of a reference goes on from the segment, so the path is not walked
            // again. A new value has no known type.
            known = if matches!(out, Out::Ref(_)) {
                after
            } else {
                None
            };
            base = Opnd::Static(out);
            // A step that selected a handle ends the segment: the next step reads the handle as
            // its base (Lean `baseData`), before its index evaluates.
            while matches!(self.opnd_seen(&base), Seen::Handle(_))
                && let Some(next) = rest.first()
            {
                known = None;
                // An `@field` reads its base after its key evaluates, so its segment starts here.
                if let Sel::Key(..) = next {
                    break;
                }
                if let Sel::Field(..) = next {
                    let (out, taken) = self.field_or_entry(base.into_out(), rest)?;
                    rest = rest.get(taken..).unwrap_or_default();
                    if rest.is_empty() {
                        return Ok(Some(out));
                    }
                    base = Opnd::Static(out);
                } else {
                    base = self.base_data(next.pos(), base.into_out())?;
                }
            }
        }
    }

    /// The base that the fields of `steps` from `done` select from `b`, while the base is not a
    /// static value, and the number of steps taken (Lean `indexBase`). A field of a root that is
    /// not static, for example a port of an instance, applies at once by the rule of `field_part`.
    fn index_base(&mut self, mut b: Out, steps: &[Sel<'_>], mut done: usize) -> Res<(Out, usize)> {
        while let Some(Sel::Field(..)) = steps.get(done)
            && !matches!(self.store.seen(&b), Seen::Static(_))
        {
            let (out, taken) = self.field_or_entry(b, steps.get(done..).unwrap_or_default())?;
            b = out;
            done += taken;
        }
        Ok((b, done))
    }

    /// The field step at the start of `steps` on the base `b`, and the number of steps taken
    /// (Lean `fieldPart` and `childSel`). A field of an `Instance` handle that names a family of
    /// the child, followed by an index, selects the entry of that key: the two steps are one
    /// selection (section 6.2). Else the field applies by the rule of `field_part`.
    fn field_or_entry(&mut self, b: Out, steps: &[Sel<'_>]) -> Res<(Out, usize)> {
        let Some(Sel::Field(q, f)) = steps.first() else {
            return Ok((b, 0));
        };
        if let Some(Sel::Index(p, [key])) = steps.get(1)
            && let Some(sym) = self.child_family(&b, f)
        {
            return Ok((self.child_sel((*p, *q), &b, (sym, &f.name), key)?, 2));
        }
        Ok((self.field_part(*q, b, f)?, 1))
    }

    /// The first segment of a read from `base` along `steps`: the result, and the number of its
    /// steps. The indices evaluate while the base waits in the store, so that an index cannot
    /// change the value that the base read. Then one walk checks and applies the steps. The
    /// checks charge nothing, so they can follow the indices, as long as no string scan charges
    /// before a later index evaluates. A string container before the last step thus ends the
    /// segment, and its index makes the base of the next one. The type of the base tells which
    /// container is a string, with no walk. A base without a known type ends the segment at each
    /// index, which is cheap: such a base is a new value, so a step takes its element.
    fn segment(
        &mut self,
        base: Opnd,
        steps: &[Sel<'_>],
        known: Option<TyId>,
    ) -> Res<(Out, usize, Option<TyId>)> {
        let mut known = known;
        let mut after = known;
        let mut keyed = Keyed::new(steps.len());
        let mut stop = None;
        let held = self.held_path(&base, known);
        let tracked = held.is_none().then(|| self.static_path(&base)).flatten();
        let on_agg = matches!(self.opnd_seen(&base), Seen::Agg(_));
        // A base that the step of an `@field` reads (Lean `baseData`) reads after the key of the
        // step evaluates and before the next key, so such a step ends its segment.
        let reads_base = matches!(
            self.opnd_seen(&base),
            Seen::Handle(Handle::Res { .. } | Handle::Input { .. }) | Seen::Pending(..)
        );
        let root = base.changing_root();
        let mut moved = None;
        let at = self.store.park(base.into_out());
        let mut held = match held {
            Some((r, ty)) => {
                self.store.cursor(at, r, true);
                Some(ty)
            }
            None => None,
        };
        let follows = tracked.is_some();
        if let Some(r) = tracked {
            self.store.cursor(at, r, false);
        }
        for (n, step) in steps.iter().enumerate() {
            // A selection of a hardware aggregate normalizes an empty part, which charges its
            // size. As in Lean, that charge comes before the next index evaluates, so the
            // segment ends before an index that follows a selection of an empty part. A part of
            // a type with a hardware leaf charges nothing, and no part before it is empty, so the
            // index can evaluate first, and one walk then takes the whole run of steps.
            if on_agg
                && n > 0
                && matches!(step, Sel::Index(..) | Sel::Key(..))
                && known.is_none_or(|t| self.tys.meta(t).leaves.is_zero())
            {
                break;
            }
            // Lean checks each step before the next key evaluates, and a key with a call can make
            // a record. So the steps before it pass their checks first, by their types, or the
            // segment ends before it and its walk checks them.
            if self.has_call(step) && !self.checked(&mut keyed) {
                break;
            }
            // A key with a call can change a `let mut` local that a waiting key reads, so the
            // waiting keys take their values first. A key that cannot fails at the walk.
            if !self.own_waiting(step, &mut keyed) {
                break;
            }
            // An index evaluates while the walk waits at the part that the earlier steps lead
            // to. At a static part the base holds the root local, as in Lean, to the end. An
            // index with no call cannot change the root, so the hold has no effect for it. For
            // an index with a call, the first change of the root decides the hold (`arm`).
            let armed = held.is_some() && self.has_call(step);
            if armed {
                self.store.arm(at, steps.len() - n);
            }
            let before = root.map(|r| self.store.changes_of(r));
            let key = self.key(step);
            if armed {
                self.store.disarm(at);
            }
            match key {
                Ok(mut k) => {
                    self.pay_named(&mut k, n == 0 && reads_base);
                    let next = held.and_then(|ty| self.held_step(ty, &k));
                    let number = if follows {
                        self.held_step(known, &k).map(|(number, _)| number)
                    } else {
                        next.map(|(number, _)| number)
                    };
                    self.store.cursor_step(at, number);
                    held = next.map(|(_, ty)| ty);
                    after = known.and_then(|t| self.key_ty(t, &k));
                    self.push_key(&mut keyed, k, known);
                    // An index that changed the root reads an old part and pays for its result
                    // (section 5.4). Its step ends the segment, so the charge is the last step.
                    if let Sel::Index(q, _) | Sel::Key(q, ..) = step
                        && root.is_some_and(|r| Some(self.store.changes_of(r)) != before)
                    {
                        moved = Some(*q);
                        break;
                    }
                    let reads_first = n == 0 && reads_base;
                    if n + 1 < steps.len()
                        && self.ends_segment(step, keyed.keys().last(), reads_first, (known, after))
                    {
                        break;
                    }
                }
                Err(e) => {
                    stop = Some(e);
                    break;
                }
            }
            known = after;
        }
        let Followed {
            out,
            at_type,
            string_last,
        } = self.followed(at, keyed.keys())?;
        let out = match moved {
            Some(q) if !string_last => self.renewed(q, out)?,
            _ => out,
        };
        if let Some(e) = stop {
            // The base of the step whose index failed is a type: that check comes first.
            if let Some(Sel::Index(q, _)) = steps.get(keyed.keys().len())
                && at_type
            {
                return fail_type_index(*q);
            }
            return Err(e);
        }
        Ok((out, keyed.keys().len(), after))
    }

    /// Pushes the evaluated step `key` on a container of the type `within` onto `keyed`. An
    /// `@field` key that refers to a `let mut` local, or to a part of one, waits in the store for
    /// the walk, so its number joins the waiting keys: a later key with a call can change the
    /// local before the walk reads it.
    fn push_key<'a>(&self, keyed: &mut Keyed<'a>, key: Key<'a>, within: Option<TyId>) {
        if let Key::Named(Named {
            key: Out::Ref(r), ..
        }) = &key
            && self.store.is_mutable(&r.root)
        {
            keyed.waiting.push(keyed.keys.len());
        }
        keyed.keys.push(key);
        keyed.within.push(within);
    }

    /// Whether each step of `keyed` passes its checks by the type of its container (`passes`).
    /// The check goes on from the last step that it passed, so it takes each step once. A key
    /// with a call then evaluates after the checks of the steps before it, as in Lean. A step that
    /// its type does not pass stops the check, and the walk of the steps gives its result.
    fn checked(&self, keyed: &mut Keyed<'_>) -> bool {
        while let (Some(key), Some(within)) = (
            keyed.keys.get(keyed.checked),
            keyed.within.get(keyed.checked),
        ) {
            if !within.is_some_and(|t| self.passes(t, key)) {
                return false;
            }
            keyed.checked += 1;
        }
        true
    }

    /// Whether the type `t` of its container shows that the evaluated step `key` passes its
    /// checks, and that its walk charges nothing: a number in the range of an array or a tuple, a
    /// selector of a tuple, or a field or a paid `@field` name that a struct declares. Only the
    /// value decides another step, for example an index of a list, and some steps fail.
    fn passes(&self, t: TyId, key: &Key<'_>) -> bool {
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Checked, 1);
        let ty = self.tys.get(t);
        let number = match key {
            Key::Index(_, _, Index::Number(k)) | Key::Named(Named { at: Some(k), .. }) => *k,
            Key::Select(_, _, index) => match index.as_str().parse::<usize>() {
                Ok(k) if matches!(ty, Ty::Tuple(_)) => k,
                _ => return false,
            },
            Key::Field(..) | Key::Named(_) => {
                return matches!(ty, Ty::Struct(_)) && self.key_ty(t, key).is_some();
            }
            Key::Index(..) => return false,
        };
        match ty {
            Ty::Array(_, len) => len.to_u64().is_some_and(|len| (number as u64) < len),
            Ty::Tuple(parts) => number < parts.len(),
            _ => false,
        }
    }

    /// Before the key of `step` evaluates, gives each waiting key of `keyed` its own value if the
    /// key of `step` has a call, as Lean reads each key at its step. The copy takes work within
    /// the charge of the key (`owns_within_charge`). Another key fails its check at the walk, and
    /// the run stops there: the result is false, and the caller applies the steps first. A step
    /// with a call leaves no key waiting.
    fn own_waiting(&mut self, step: &Sel<'_>, keyed: &mut Keyed<'_>) -> bool {
        if keyed.waiting.is_empty() || !self.has_call(step) {
            return true;
        }
        for at in keyed.waiting.drain(..) {
            #[cfg(test)]
            crate::counters::add(crate::counters::Count::Waited, 1);
            let Some(Key::Named(n)) = keyed.keys.get_mut(at) else {
                continue;
            };
            if !Self::owns_within_charge(n, self.store.value(&n.key)) {
                return false;
            }
            let key = std::mem::replace(&mut n.key, Out::Made(Val::Static(Value::Unit)));
            n.key = Out::Made(self.store.take(key));
        }
        true
    }

    /// Whether a copy of the key `value` of the step `n` takes work within the charge of the key: a
    /// number of one word, a name that its step paid, or a paid `PortKey` whose index has at most
    /// 32 bits. Each other key fails its check at the walk.
    fn owns_within_charge(n: &Named<'_>, value: &Value) -> bool {
        match value {
            Value::Int(_) => n.at.is_some(),
            Value::Str(_) => n.paid,
            Value::Record(_, fields) => {
                n.paid && matches!(fields.as_slice(), [.., Value::Int(k)] if k.fits_unsigned(32))
            }
            _ => false,
        }
    }

    /// Whether the key of the step can change a local of its frame while it evaluates: it holds a
    /// call. The scan marked it.
    fn has_call(&self, step: &Sel<'_>) -> bool {
        match step {
            Sel::Index(_, args) => self.call_args.has_call(args),
            Sel::Key(_, _, key) => self.call_args.has_call(std::slice::from_ref(key)),
            Sel::Select(..) | Sel::Field(..) => false,
        }
    }

    /// Pays the name of the step `key` of an `@field` at its step, unless its base reads first.
    fn pay_named(&mut self, key: &mut Key<'_>, reads_first: bool) {
        if let Key::Named(named) = key
            && named.charges
            && !reads_first
        {
            self.pay_early(named);
        }
    }

    /// Whether the evaluated step `step` with the key `key`, on a container of the type `known`,
    /// ends the segment because the next step must see its result first. A step of an `@field`
    /// ends it when it reads its base (`reads_first`) or when the charge of its name waits: the
    /// charge comes before the next key evaluates. A part of the type `after` that is a handle
    /// ends it, because the next step reads the handle before its index evaluates. A string
    /// container ends it at an index, because the scan of the string charges before a later
    /// index evaluates. A step on a base of unknown type ends it too: that base is a new value,
    /// and its part can be an instance, which the next step reads as a handle before it applies.
    /// This one rule covers the index, the selector, and the field.
    fn ends_segment(
        &self,
        step: &Sel<'_>,
        key: Option<&Key<'_>>,
        reads_first: bool,
        (known, after): (Option<TyId>, Option<TyId>),
    ) -> bool {
        if matches!(key, Some(Key::Named(m)) if reads_first || (m.charges && !m.paid))
            || after.is_some_and(|t| self.tys.get(t).is_handle())
        {
            return true;
        }
        match step {
            Sel::Index(..) | Sel::Key(..) => {
                known.is_none_or(|t| matches!(self.tys.get(t), Ty::String))
            }
            Sel::Select(..) | Sel::Field(..) => known.is_none(),
        }
    }

    /// The walk of the segment that waited at `at` along its evaluated steps `keyed`. A step that
    /// goes into a list a change reached splits the walk: the first steps walk the live local, and
    /// only the part where they end gets a copy of its old value.
    pub(super) fn followed(&mut self, at: usize, keyed: &[Key<'_>]) -> Res<Followed> {
        let (parked, mark, split) = self.store.unpark(at);
        let followed = match split {
            Some(n) => {
                let (first, rest) = keyed.split_at(n.min(keyed.len()));
                self.follow_crossed(parked, first, rest, mark.as_ref())
            }
            None => self.follow(Opnd::of_out(parked), keyed, mark.as_ref()),
        };
        if let Some(mark) = &mark {
            self.store.finish(mark);
        }
        followed
    }

    /// The path that follows the steps of a segment from a part of an aggregate root of a local,
    /// with the type of its part, or `None` if the base is no such part. An index that waits at a
    /// static part of the root holds the root local.
    fn held_path(&self, base: &Opnd, ty: Option<TyId>) -> Option<(Ref, Option<TyId>)> {
        let Opnd::Static(Out::Ref(r)) = base else {
            return None;
        };
        (matches!(r.root, Root::Local(..)) && matches!(self.store.root(&r.root), Val::Agg(_)))
            .then(|| (r.clone(), ty))
    }

    /// The reference of a base that is a part of a static local. The read follows the numbers of
    /// its steps, so its result resolves at the part where it ends.
    fn static_path(&self, base: &Opnd) -> Option<Ref> {
        let Opnd::Static(Out::Ref(r)) = base else {
            return None;
        };
        (matches!(r.root, Root::Local(..)) && matches!(self.store.root(&r.root), Val::Static(_)))
            .then(|| r.clone())
    }

    /// The number of the step `key`, which the walk takes from a part of type `ty`, and the type
    /// of the part that follows. A dynamic index or a field without a number ends the path: no
    /// static part follows it.
    pub(super) fn held_step(
        &self,
        ty: Option<TyId>,
        key: &Key<'_>,
    ) -> Option<(usize, Option<TyId>)> {
        let k = match key {
            Key::Index(_, _, Index::Number(k)) => Some(*k),
            Key::Index(..) => None,
            Key::Select(_, _, index) => index.as_str().parse::<usize>().ok(),
            Key::Field(_, f) => ty
                .and_then(|t| self.tys.parts(t))
                .and_then(|parts| self.field_number(parts.item()?, f)),
            // A name reads only after its size charge, so only a number names the part here.
            Key::Named(n) => self.named_slot(ty, n),
        }?;
        Some((k, ty.and_then(|t| self.part_ty(t, k))))
    }

    /// The type of a base that refers to a local or a constant: the type of its root, along its
    /// path. A new value has no known type here.
    fn base_ty(&self, base: &Opnd) -> Option<TyId> {
        let Opnd::Static(Out::Ref(r)) = base else {
            return None;
        };
        let mut t = self.store.root_ty(&r.root)?;
        for &k in &r.path {
            t = self.part_ty(t, k)?;
        }
        Some(t)
    }

    /// The type of the part `k` of a container of type `t`.
    pub(super) fn part_ty(&self, t: TyId, k: usize) -> Option<TyId> {
        self.tys
            .part(t, k)
            .or_else(|| self.tys.parts(t).and_then(|p| p.types.get(k).copied()))
    }

    /// The type of the part that the evaluated step `key` selects in a container of type `t`.
    pub(super) fn key_ty(&self, t: TyId, key: &Key<'_>) -> Option<TyId> {
        match key {
            Key::Index(_, _, Index::Number(k)) => self.part_ty(t, *k),
            Key::Index(..) => None,
            Key::Select(_, _, index) => self.part_ty(t, index.as_str().parse().ok()?),
            Key::Field(_, f) => {
                let parts = self.tys.parts(t)?;
                parts
                    .types
                    .get(self.field_number(parts.item()?, f)?)
                    .copied()
            }
            Key::Named(n) => self.part_ty(t, self.named_slot(Some(t), n)?),
        }
    }

    /// The result `out` of a read, as the window left the part it refers to. The steps of the
    /// read have walked: the part is the one where the read ends, or the list where a split walk
    /// stops, and it resolves here.
    fn resolve_ref(&mut self, mark: Option<&Mark>, out: Out) -> Out {
        let Some(mark) = mark else {
            return out;
        };
        self.store.resolved(out, *mark)
    }

    /// The walk of a read along the evaluated indices `keyed`, in one pass: the result, and
    /// whether the container after the last step is a type. A string container ends a segment:
    /// its index makes a new string, which is the base of the next segment.
    fn follow(&mut self, base: Opnd, keyed: &[Key<'_>], mark: Option<&Mark>) -> Res<Followed> {
        let mut base = base;
        let mut string_last = false;
        let mut rest = keyed;
        let mut mark = mark;
        loop {
            // An `@field` step that needs its whole base takes it as a result: a handle, or a name
            // that waits for its charge. The steps after it go on from its part.
            while let Some(Key::Named(n)) = rest.first()
                && self.named_whole(n, &base)
            {
                let out = self.named_step(base.into_out(), n)?;
                rest = rest.get(1..).unwrap_or_default();
                if rest.is_empty() {
                    return Ok(Followed::new(self.resolve_ref(mark, out), false, false));
                }
                base = Opnd::of_out(out);
            }
            // The steps through the nodes of a stored root go on from the part that the last step
            // found, so the whole run walks the path from the root once.
            let (through, taken) = self.node_steps(base, rest);
            base = through;
            rest = rest.get(taken..).unwrap_or_default();
            if taken > 0 && rest.is_empty() {
                return Ok(Followed::new(
                    self.resolve_ref(mark, base.into_out()),
                    false,
                    false,
                ));
            }
            // The steps on an aggregate each give a part in constant work, so they take no walk
            // along a path. A part that is not an aggregate ends them.
            while let Some(key) = rest.first()
                && matches!(self.opnd_seen(&base), Seen::Agg(_))
            {
                let out = match key {
                    Key::Named(n) => self.named_step(base.into_out(), n)?,
                    key => self.agg_key(base.into_out(), key)?,
                };
                rest = rest.get(1..).unwrap_or_default();
                if rest.is_empty() {
                    return Ok(Followed::new(self.resolve_ref(mark, out), false, false));
                }
                base = Opnd::of_out(out);
            }
            let mut cur = self.opnd_seen(&base);
            let mut numbers = Vec::with_capacity(rest.len());
            let mut string_step = None;
            let mut name_step = None;
            for (at, key) in rest.iter().enumerate() {
                let number = match key {
                    Key::Index(q, ..) if matches!(cur, Seen::Static(Value::Type(_))) => {
                        return fail_type_index(*q);
                    }
                    Key::Index(..) if matches!(cur, Seen::Static(Value::Str(_))) => {
                        string_step = Some(at);
                        break;
                    }
                    // A name that waits for its charge pays in `named_step`, after its checks and
                    // before its look-up, so the run ends before it.
                    Key::Named(n) if n.charges && !n.paid => {
                        name_step = Some(at);
                        break;
                    }
                    Key::Named(n) => self.named_number(n, cur)?.0,
                    key => self.step_at(key, cur)?.0,
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
            let out = self.resolve_ref(mark, out);
            if let Some(at) = name_step {
                base = Opnd::of_out(out);
                rest = rest.get(at..).unwrap_or_default();
                mark = None;
                continue;
            }
            let Some(at) = string_step else {
                return Ok(Followed::new(out, at_type, string_last));
            };
            let Some(Key::Index(q, xp, i)) = rest.get(at) else {
                return Ok(Followed::new(out, at_type, string_last));
            };
            base = Opnd::Static(self.str_at(*q, *xp, &out, i)?);
            rest = rest.get(at + 1..).unwrap_or_default();
            string_last = rest.is_empty();
            mark = None;
        }
    }

    /// The result `out` of the index at `q` that changed its own root: it charges its size as the
    /// last step of the read, and then it is a new value, so a binding of it is no copy.
    fn renewed(&mut self, q: Pos, out: Out) -> Res<Out> {
        let size = self.size(&out);
        self.charge(q, size)?;
        Ok(Out::Made(self.store.take(out)))
    }

    /// The walk of a read whose steps go into a list that a change reached: `first` leads to the
    /// list, and `rest` starts with the step into it. An index in the old range of the list
    /// resolves the element alone, so no copy of the list is made. Else the read copies the list
    /// as it was, which gives the error of the step.
    fn follow_crossed(
        &mut self,
        parked: Out,
        first: &[Key<'_>],
        rest: &[Key<'_>],
        mark: Option<&Mark>,
    ) -> Res<Followed> {
        let list = self.follow(Opnd::of_out(parked), first, None)?.out;
        let step = rest.first().and_then(|key| match key {
            Key::Index(_, _, Index::Number(j)) => Some(*j),
            Key::Named(n) => n.at,
            _ => None,
        });
        if let (Some(mark), Some(j), Out::Ref(r)) = (mark, step, &list)
            && self
                .store
                .old_len(*mark, &r.path)
                .is_some_and(|len| j < len)
        {
            let element = elem(Opnd::Static(list), j);
            let out = self.resolve_ref(Some(mark), element);
            return self.follow(Opnd::of_out(out), rest.get(1..).unwrap_or_default(), None);
        }
        let list = self.resolve_ref(mark, list);
        self.follow(Opnd::of_out(list), rest, None)
    }

    /// The longest run of steps of `keys` that stay inside the nodes of an aggregate root, taken
    /// with a cursor: the part that a step finds is the container of the next step, so the run
    /// walks the path of `base` from the root once, and each step takes constant work. A step
    /// that fails its check, or that finds a reference to normalize, ends the run before it, so
    /// the step of `agg_key` gives its error or its charge. The result is the reference to the
    /// part where the run ended, and the number of steps taken.
    fn node_steps(&mut self, base: Opnd, keys: &[Key<'_>]) -> (Opnd, usize) {
        let Opnd::Static(Out::Ref(r)) = &base else {
            return (base, 0);
        };
        let mut taken: Vec<usize> = Vec::new();
        let mut cur = self.store.at(r);
        for key in keys {
            let Some((k, next)) = self.node_step(cur, key) else {
                break;
            };
            taken.push(k);
            cur = next;
        }
        let count = taken.len();
        match base {
            Opnd::Static(Out::Ref(mut r)) if count > 0 => {
                r.path.extend(taken);
                (Opnd::Static(Out::Ref(r)), count)
            }
            base => (base, 0),
        }
    }

    /// The step `key` from the container node `cur`, if the step stays inside the nodes of a
    /// stored root: the number of the part and the part. A step that fails its check, or that
    /// finds a reference to normalize, is no such step, so `agg_key` gives its error or its
    /// charge.
    pub(super) fn node_step<'s>(&self, cur: Seen<'s>, key: &Key<'_>) -> Option<(usize, Seen<'s>)> {
        let Seen::Agg(a @ (Agg::Array(..) | Agg::Tuple(..) | Agg::Record(..) | Agg::List(..))) =
            cur
        else {
            return None;
        };
        let k = self.node_key(a, key)?;
        self.node_next(cur, k)
    }

    /// The part `k` of the container node `cur`, if the step stays inside the nodes of a stored
    /// root: a part that is a reference to normalize is no such step.
    pub(super) fn node_next<'s>(&self, cur: Seen<'s>, k: usize) -> Option<(usize, Seen<'s>)> {
        let next = self.store.step(cur, k);
        if let Seen::Agg(Agg::Ref(_, t)) = next
            && (self.tys.meta(*t).leaves.is_zero()
                || matches!(self.tys.get(*t), Ty::Bool | Ty::UInt(_) | Ty::SInt(_)))
        {
            return None;
        }
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Selected, 1);
        Some((k, next))
    }

    /// The number of the part that the step `key` takes from the node `a`, if the step passes
    /// its checks.
    fn node_key(&self, a: &Agg, key: &Key<'_>) -> Option<usize> {
        match (key, a) {
            (
                Key::Index(_, _, Index::Number(k)),
                Agg::Array(_, p) | Agg::Tuple(_, p) | Agg::List(_, p),
            ) => (*k < p.0.len()).then_some(*k),
            (Key::Select(_, _, index), Agg::Tuple(_, p)) => index
                .as_str()
                .parse::<usize>()
                .ok()
                .filter(|k| *k < p.0.len()),
            (Key::Field(_, f), Agg::Record(..)) => self.agg_field_at(a, f).map(|(k, _)| k),
            (Key::Named(n), Agg::Array(_, p) | Agg::Tuple(_, p) | Agg::List(_, p)) => {
                n.at.filter(|k| *k < p.0.len())
            }
            (Key::Named(n), Agg::Record(..)) => self.named_agg_field(n, a),
            _ => None,
        }
    }

    /// The step `key` on the aggregate `b`.
    pub(super) fn agg_key(&mut self, b: Out, key: &Key<'_>) -> Res<Out> {
        match key {
            Key::Index(q, xp, i) => self.agg_index(*q, *xp, b, i),
            Key::Select(q, r, index) => self.agg_select(*q, *r, index, b),
            Key::Field(q, f) => self.agg_field(*q, f, b),
            Key::Named(n) => self.named_step(b, n),
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
        let n = match self.base_data(pos, v)? {
            Opnd::Static(o) if matches!(self.store.seen(&o), Seen::Agg(_)) => {
                return self.agg_len(pos, &o);
            }
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
        self.store.shut_window(place.root);
        let y = if let Some(t) = place.ty {
            self.typed_use(pos, t, o.is_ref(), o, Whole)?
        } else {
            self.held_use(pos, &place, o)?
        };
        self.store_at(pos, value.pos(), &place, y)?;
        Ok(None)
    }

    /// The assignment at `pos` of the result `o` to the place of a local without a type that
    /// holds a value (section 5.4). The local has the type of its value. A handle with a handle
    /// type thus gets the typed use at that type (`typed_use`). Another value keeps its form
    /// after the copy (`same_form`). A local that holds an own output takes only an own output
    /// of the same data type. Its text names the fix: use the output directly.
    fn held_use(&mut self, pos: Pos, place: &Place, o: Out) -> Res<Val> {
        let held = match self.store.current(place.root, &place.keys) {
            Seen::Handle(h) => Some(h.clone()),
            _ => None,
        };
        if let Some(t) = held.as_ref().and_then(|h| self.handle_ty(h)) {
            return self.typed_use(pos, t, o.is_ref(), o, Whole);
        }
        self.copy(pos, &o)?;
        let old = self.store.current(place.root, &place.keys);
        let new = self.store.seen(&o);
        if same_form(old, new) {
            return Ok(self.store.take(o));
        }
        if let Seen::Handle(Handle::Res {
            kind: Resource::Output,
            ty,
            path,
            ..
        }) = old
        {
            let r = str_text(&self.paths.source(*path, &self.syms.texts));
            return fail(
                Code::S010,
                pos,
                format!(
                    "the local holds the output `{r}`, so it takes only an output of `{}`, not \
                     {}; use the output `{r}` directly",
                    self.tys.text(*ty),
                    self.about(new)
                ),
            );
        }
        fail(
            Code::S010,
            pos,
            format!(
                "expected {}, but the value is {}",
                self.text(old),
                self.text(new)
            ),
        )
    }

    /// The place `target` at `pos` (section 5.2). Its root is a `let mut` local, else the error
    /// is `code` at `pos`. The root name charges nothing. Then the place opens a window of its
    /// root, which the caller closes (`shut_window`), and a root with an open window is `S008`
    /// at `pos` (section 9.1). Each step charges 1 at its node, then
    /// its index evaluates, from the root outward.
    ///
    /// Lean checks the container and the index of each step before the next step charges.
    /// Here the checks run in one walk along the path after the indices, so no step walks
    /// again from the root. `S008` keeps the root unchanged while the indices evaluate, and
    /// a failed check comes before an error of a later step. Thus the first error is that of
    /// Lean. A key with a call can make a record, so the steps before it pass their checks by
    /// their types first (`checked`), or the walk catches up before it.
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
                .slot(id)
                .filter(|s| s.mutable)
                .map(|s| (id, s.ty)),
            _ => None,
        };
        let Some((id, slot_ty)) = found else {
            return bad();
        };
        let frame = self.store.frame_index();
        let root = Root::Local(frame, id);
        if !self.store.open_window(root) {
            return fail(
                Code::S008,
                pos,
                "the root of the place is pending in a window".to_owned(),
            );
        }
        let aggregate = matches!(self.store.root(&root), Val::Agg(_));
        let mut state = Walked::start(slot_ty);
        let mut keyed = Keyed::new(steps.len());
        let mut part_ty = slot_ty;
        // The type of the part for the test of an `Instance` handle: a root without a declared
        // type has the type that its node stores.
        let mut shape = slot_ty.or_else(|| match self.store.root(&root) {
            Val::Agg(a) => a.stored_ty(),
            _ => None,
        });
        let mut stop = None;
        for (n, step) in steps.iter().enumerate() {
            // Lean checks each step before the next step charges, and a key with a call can make
            // a record. So the steps before it pass their checks first, by their types, or the
            // walk catches up.
            if self.has_call(step) && !self.checked(&mut keyed) {
                state = self.walk(root, state, keyed.keys(), false)?;
                keyed.clear();
            }
            // A key with a call can change a `let mut` local that a waiting key reads, so the
            // waiting keys take their values first. A key that cannot fails at the walk.
            if !self.own_waiting(step, &mut keyed) {
                state = self.walk(root, state, keyed.keys(), false)?;
                keyed.clear();
            }
            // A step into a reference normalizes an empty part, which charges its size. As in
            // Lean, that comes before the next step charges, so the walk catches up first.
            if aggregate
                && !state.settled
                && !keyed.keys().is_empty()
                && part_ty.is_some_and(|t| self.tys.meta(t).leaves.to_u64() == Some(0))
            {
                state = self.walk(root, state, keyed.keys(), false)?;
                keyed.clear();
            }
            // A field of an `Instance` handle is a port, which a place cannot select. The step
            // charges after the index that follows it (Lean `placePort`), so the walk catches up
            // to see the part.
            if let Sel::Field(fp, f) = step
                && self.may_be_instance(shape, aggregate)
            {
                state = self.walk(root, state, keyed.keys(), false)?;
                keyed.clear();
                if let Some(info) = self.instance_at(root, &state) {
                    return self.place_port(info, (*fp, f), steps.get(n + 1..).unwrap_or_default());
                }
            }
            match self.charge(step.pos(), 1).and_then(|()| self.key(step)) {
                Ok(mut k) => {
                    // A place reads no base, so the name of an `@field` pays at its step.
                    self.pay_named(&mut k, false);
                    let within = part_ty;
                    part_ty = part_ty.and_then(|t| self.key_ty(t, &k));
                    shape = shape.and_then(|t| self.key_ty(t, &k));
                    // A name that the fuel could not pay ends the walk of the steps: the checks of
                    // its step come first, and then its charge fails before a later node charges.
                    let unpaid = matches!(&k, Key::Named(n) if n.charges && !n.paid);
                    self.push_key(&mut keyed, k, within);
                    if unpaid {
                        break;
                    }
                }
                Err(e) => {
                    stop = Some(e);
                    break;
                }
            }
        }
        let walked = self.walk(root, state, keyed.keys(), true)?;
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
            part: walked.part,
            own: walked.own,
        })
    }

    /// Whether the part of a place can be an `Instance` handle: its type says so, or a root of
    /// nodes has no type to tell.
    fn may_be_instance(&self, shape: Option<TyId>, aggregate: bool) -> bool {
        shape.map_or(aggregate, |t| matches!(self.tys.get(t), Ty::Instance(_)))
    }

    /// The `Instance` handle that the part after the walk `st` is, if it is one.
    fn instance_at(&self, root: Root, st: &Walked) -> Option<InstInfo> {
        let seen = match &st.own {
            Some(v) => v.seen(),
            None => self.store.current(root, &st.keys),
        };
        match seen {
            Seen::Handle(Handle::Inst { id, path, inst, ty }) => Some(InstInfo {
                id: *id,
                path: *path,
                inst: *inst,
                ty: *ty,
            }),
            _ => None,
        }
    }

    /// A mutation at `pos` of a binding `id` of the current frame (section 9.4). The binding is older
    /// than the innermost guard when that guard started at the current depth: `S016`.
    pub(super) fn mutation(&self, pos: Pos, id: DeclId) -> Res<()> {
        if let Some(guard) = self.guard
            && guard.depth == self.depth
        {
            return fail(Code::S016, pos, guard.change(&self.file.decl(id).name));
        }
        Ok(())
    }

    /// Writes `y` into the place (section 5.2). A place without a step binds its root again, so
    /// a hardware value gets the next version of the root. A place with a step checks the new
    /// depth of the root: the number of steps plus the depth of the value (`S015` at `pos`).
    /// Then it writes into the live value of the root, and a root that has a hardware leaf
    /// afterwards binds again (`rebind`). A step into a list makes a value with a hardware leaf
    /// `S011` at `q`, the node of the value.
    pub(super) fn store_at(&mut self, pos: Pos, q: Pos, place: &Place, y: Val) -> Res<()> {
        if place.keys.is_empty() {
            let y = self.named(pos, place.id, y)?;
            self.charge_held(pos, place.root)?;
            self.store.rebind_local(place.root, y);
            return Ok(());
        }
        if place.in_list && y.has_hw(&self.tys) {
            return fail(
                Code::S011,
                q,
                "a list holds no value with a hardware leaf".to_owned(),
            );
        }
        let x = self.item(q, y)?;
        // The root is within the nesting depth, so only the value on the path can raise it.
        self.bounded(pos, place.keys.len() as u64 + x.depth(&self.tys))?;
        let static_root = matches!(self.store.root(&place.root), Val::Static(_));
        match x {
            Agg::Static(w) if static_root => {
                self.charge_held(pos, place.root)?;
                self.store.replace_part(place.root, &place.keys, w);
                Ok(())
            }
            x if static_root || matches!(self.store.root(&place.root), Val::Agg(_)) => {
                self.rebind(pos, place, x)
            }
            _ => fail(
                Code::S010,
                pos,
                "the place has no part for its value".to_owned(),
            ),
        }
    }

    /// The step `step` of a place or a read with its index, which gets its static check.
    pub(super) fn key<'a>(&mut self, step: &Sel<'a>) -> Res<Key<'a>> {
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
                let xp = i.pos();
                self.check_static(xp, &o)?;
                Ok(Key::Index(q, xp, self.index_of(&o)))
            }
            Sel::Select(q, r, index) => Ok(Key::Select(q, r, index)),
            Sel::Field(q, f) => Ok(Key::Field(q, f)),
            Sel::Key(q, base, key) => self.named_key(q, base, key, None),
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
    fn walk(&mut self, root: Root, mut st: Walked, keyed: &[Key<'_>], last: bool) -> Res<Walked> {
        let aggregate = matches!(self.store.root(&root), Val::Agg(_));
        let mut cur = match st.own.take() {
            Some(v) => Cur::Own(v),
            None => Cur::In(self.store.current(root, &st.keys)),
        };
        let mut known = st.known;
        let mut in_list = st.in_list;
        let mut keys = std::mem::take(&mut st.keys);
        for key in keyed {
            let seen = cur.seen();
            // A name that the fuel could not pay at its step fails here, after its checks.
            if let Key::Named(n) = key
                && !n.paid
            {
                let plan = self.named_plan(n, At::Seen(seen), self.store.value(&n.key))?;
                Self::pay_unpaid(&mut self.fuel, n, &plan)?;
            }
            let (k, field) = self.step_at(key, seen)?;
            known = match (field, known, seen) {
                (Some(ft), _, _) => Known::Ty(ft),
                (None, Known::Ty(t), _) => self.tys.part(t, k).map_or(Known::Absent, Known::Ty),
                (
                    None,
                    Known::Element,
                    Seen::Static(Value::Array(elem, _) | Value::List(elem, _)),
                ) => Known::Ty(*elem),
                (None, Known::Absent | Known::Element, _) => Known::Element,
            };
            in_list = in_list
                || matches!(
                    seen,
                    Seen::Static(Value::List(..)) | Seen::Agg(Agg::List(..))
                );
            // A step into a reference makes a new reference to the part, in constant work.
            let lazy = match seen {
                Seen::Agg(Agg::Ref(b, t)) => Some((b.clone(), *t)),
                _ => None,
            };
            cur = if let Some((base, t)) = lazy {
                drop(cur);
                Cur::Own(self.lazy_part(key_pos(key), &base, t, k, key, field)?)
            } else {
                match cur {
                    Cur::In(s) => Cur::In(self.store.step(s, k)),
                    Cur::Own(Val::Static(mut x)) => Cur::Own(Val::Static(take_element(&mut x, k))),
                    own @ Cur::Own(_) => own,
                }
            };
            keys.push(k);
        }
        if !last {
            return Ok(Walked {
                keys,
                known,
                in_list,
                settled: matches!(cur.seen(), Seen::Static(_)),
                own: cur.into_own(),
                ..Walked::start(None)
            });
        }
        let seen = cur.seen();
        let held = self.held_of(seen);
        // A static part of the live root has no stored size: `push` and `pop` need none, and a
        // rebind reads it once when it charges (`part: None`).
        let part = aggregate
            .then(|| match (&cur, seen) {
                (_, Seen::Agg(a)) => Some(PartInfo {
                    size: a.size(&self.graph, &self.tys),
                    leaves: a.leaves(&self.tys),
                }),
                (Cur::In(_), Seen::Static(_)) => None,
                (Cur::Own(_), Seen::Static(v)) => Some(PartInfo {
                    size: v.size(),
                    leaves: 0,
                }),
                (_, Seen::Hw(h)) => Some(PartInfo {
                    size: self.graph.size(h),
                    leaves: 1,
                }),
                _ => Some(PartInfo { size: 1, leaves: 0 }),
            })
            .flatten();
        let ty = match known {
            Known::Ty(t) => Some(t),
            Known::Absent => None,
            Known::Element => seen.ty(&self.graph, &mut self.tys),
        };
        Ok(Walked {
            keys,
            known,
            ty,
            in_list,
            held,
            part,
            own: cur.into_own(),
            settled: false,
        })
    }

    /// What the part `seen` of a place is, for the operations that change it in place: a static
    /// list or a list node with its element type and its length, else another part.
    fn held_of(&self, seen: Seen<'_>) -> Held {
        match seen {
            Seen::Static(Value::List(elem, xs)) => Held::List {
                elem: *elem,
                len: xs.len(),
            },
            Seen::Agg(Agg::List(n, p)) => match self.tys.get(n.ty) {
                Ty::List(elem) => Held::List {
                    elem: *elem,
                    len: p.0.len(),
                },
                _ => Held::Other,
            },
            _ => Held::Other,
        }
    }

    /// The part `k` of the reference to `base` of type `t` that the step `key` selects, in its
    /// normal form. A part without a hardware leaf charges its zero size first (`normalize`).
    /// `field` is the type of the field that a field step found.
    fn lazy_part(
        &mut self,
        pos: Pos,
        base: &crate::agg::Base,
        t: TyId,
        k: usize,
        key: &Key<'_>,
        field: Option<TyId>,
    ) -> Res<Val> {
        let (part, step) = match key {
            Key::Field(_, f) => {
                let Some(sym) = self.field_sym(f) else {
                    return fail(
                        Code::S010,
                        pos,
                        format!("the field `{}` has no symbol", f.name),
                    );
                };
                (field, Step::User(sym))
            }
            Key::Named(n) if field.is_some() => {
                let Some(sym) = self.named_sym(n) else {
                    let name = match self.store.value(&n.key) {
                        Value::Str(name) => name.as_str(),
                        _ => "",
                    };
                    return fail(
                        Code::S010,
                        pos,
                        format!("the field `{}` has no symbol", str_text(name)),
                    );
                };
                (field, Step::User(sym))
            }
            _ => (self.tys.part(t, k), Step::Elem(k as u64)),
        };
        let Some(part) = part else {
            return fail(Code::S010, pos, "the part has no type".to_owned());
        };
        let offset = self.tys.offset(t, k as u64);
        let sub = base.sub(&mut self.paths, step, offset);
        self.normalize(pos, Agg::Ref(sub, part))
    }

    /// The part of a container that the value `v` at `pos` gives. A handle is a handle leaf.
    fn item(&self, pos: Pos, v: Val) -> Res<Agg> {
        match Agg::of_val(v) {
            Ok(a) => Ok(a),
            Err(Val::Pending(q, _)) => super::no_type(q),
            Err(v) => fail(
                Code::S010,
                pos,
                format!("{} is not data", self.text(v.seen())),
            ),
        }
    }
}

/// A selector in a message, with at most 256 bits of a large number.
pub(super) fn selector_text(index: &Nat) -> String {
    Int::from_decimal(index.as_str()).map_or_else(|| index.as_str().to_owned(), |n| int_text(&n))
}
