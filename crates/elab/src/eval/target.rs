// SPDX-License-Identifier: Apache-2.0
//! The part that a `:=` target selects (Lean `Elab.targetPart`, design sections 5.2 and 9.4). As in
//! a place, the indices come first, and one walk from the root then selects. A root that is not a
//! local evaluates first. Each index step charges 1, evaluates its index, and gets the static
//! check. Each index evaluates in a structural context (section 9.4). A local root gives its
//! live value after them. The walk then runs the steps from the root outward, and the static type
//! of each base decides. A base that is not an `Instance`
//! handle and has no handle flag is `S017` at the start of the target. A field of an `Instance`
//! handle selects a child input with no charge. A field and a selector `.N` of a container of a
//! type with the handle flag charge 1, then the step gets the checks of a selection. The target
//! is an identity, so it opens no window and charges no held root.

use super::inst::{child_key, family_value};
use super::place::{Key, Sel, chain, key_pos};
use super::{Evaluator, GuardKind, Out, Res, fail, need};
use crate::Code;
use crate::hw::{Handle, Ref, Root, Seen, Val};
use crate::types::TyId;
use parse::ast::{Expr, Ident, Pos};
use resolve::{DeclId, Target as Resolved};

/// The `S017` text "Part as a `:=` target" of section 6.2.
const PART_TEXT: &str = "a `:=` target is a whole resource, not a part of a value; bind the whole \
                         resource, for example `r := P(a, b);`";

impl Evaluator<'_> {
    /// The value that the `:=` target `e` selects. A local root is a reference to its slot. Another
    /// root has no slot, so it evaluates, and its value names it in the text of `S017`.
    pub(super) fn target_part(&mut self, e: &Expr) -> Res<Out> {
        let (root, steps) = chain(e).unwrap_or((e, Vec::new()));
        if let Expr::Name { pos, id, name } = root
            && let Some(family) = self.family_of(*id)
        {
            return self.family_target(e.pos(), (*pos, name, family), &steps);
        }
        let local = match root {
            Expr::Name { id, .. } => match self.target(*id) {
                Some(Resolved::Decl(decl)) if self.store.slot(decl).is_some() => Some(decl),
                _ => None,
            },
            _ => None,
        };
        let start = if let Some(decl) = local {
            Err(decl)
        } else {
            let out = self.eval(root)?;
            Ok(need(root, out)?)
        };
        let (keys, fams) = self.target_keys(&steps)?;
        let cur = match start {
            Ok(out) => out,
            Err(decl) => Out::Ref(Ref {
                root: Root::Local(self.store.frame_index(), decl),
                path: Vec::new(),
            }),
        };
        self.target_walk(e.pos(), cur, (&keys, &fams))
    }

    /// The index of each step of a target, in source order (Lean `targetKeys`). An index step
    /// charges 1, then its index evaluates in a structural context and is static (`S011`).
    fn target_keys<'e>(&mut self, steps: &[Sel<'e>]) -> Res<(Vec<Key<'e>>, Vec<Option<Out>>)> {
        let mut keys = Vec::with_capacity(steps.len());
        let mut fams = Vec::with_capacity(steps.len());
        let mut after_field = false;
        for step in steps {
            let named = std::mem::replace(&mut after_field, matches!(step, Sel::Field(..)));
            if matches!(step, Sel::Index(..)) {
                self.charge(step.pos(), 1)?;
            }
            let Sel::Index(q, args) = *step else {
                keys.push(self.key(step)?);
                fams.push(None);
                continue;
            };
            let [i] = args else {
                return fail(
                    Code::S010,
                    q,
                    "an index of a value has one argument".to_owned(),
                );
            };
            let o = self.guarded(GuardKind::Index, |ev| {
                let o = ev.eval(i)?;
                need(i, o)
            })?;
            self.check_static(i.pos(), &o)?;
            keys.push(Key::Index(q, i.pos(), self.index_of(&o)));
            // The key after a field can be the key of a family entry of a child. The guard keeps
            // the value in place, so `child_target` reads it from there.
            fams.push(named.then_some(o));
        }
        Ok((keys, fams))
    }

    /// The part that the `:=` target with the start `start` selects, when its root is the own
    /// family `x` with the binder `family` at `rp` (section 5.2). The first index takes the key
    /// checks of a family selection. Then the other indices evaluate, and the key selects the
    /// entry, as a local root gives its value. A family root without a first index is `S010`
    /// "Family as a value" at the root, after the indices.
    fn family_target(
        &mut self,
        start: Pos,
        (rp, x, family): (Pos, &str, DeclId),
        steps: &[Sel<'_>],
    ) -> Res<Out> {
        if let Some(&Sel::Index(q, [i])) = steps.first() {
            self.charge(q, 1)?;
            let o = self.key_out(i)?;
            let k = self.selection_key(rp, i.pos(), x, &o)?;
            let (keys, fams) = self.target_keys(steps.get(1..).unwrap_or_default())?;
            let v = self.entry_val(i.pos(), x, family, k)?;
            return self.target_walk(start, Out::Named(v), (&keys, &fams));
        }
        self.target_keys(steps)?;
        family_value(rp, x)
    }

    /// The walk of the steps `keys` of a target that starts at `start`, from the base `cur`
    /// outward (Lean `targetWalk`). A field that names a family of the child behind `cur` waits
    /// for the next step, whose key selects the entry (`child_target`), so the walk does not start
    /// again from the root. Else that step is `S010` "Family as a value" at `start`.
    fn target_walk(
        &mut self,
        start: Pos,
        mut cur: Out,
        (keys, fams): (&[Key<'_>], &[Option<Out>]),
    ) -> Res<Out> {
        let mut at = 0;
        while let Some(key) = keys.get(at) {
            if let Key::Field(_, f) = key
                && self.child_family(&cur, f)
            {
                let (Some(Key::Index(_, xp, _)), Some(Some(ko))) =
                    (keys.get(at + 1), fams.get(at + 1))
                else {
                    return family_value(start, &f.name);
                };
                cur = self.child_target(start, &cur, f, (*xp, ko))?;
                at += 2;
                continue;
            }
            let (out, taken) = self.target_run(cur, keys.get(at..).unwrap_or_default())?;
            cur = out;
            at += taken;
            if taken == 0 {
                cur = self.target_step(start, cur, key)?;
                at += 1;
            }
        }
        Ok(cur)
    }

    /// The longest run of steps of `keys` through containers of a type with the handle flag,
    /// from the reference `base`: the reference to the part where the run ends, and the number
    /// of steps taken. One cursor walks the path of `base` from the root, so each step takes
    /// constant work. The checks read no node that a charge changes, so they run before the
    /// charges of the run, and the first step that fails ends the run before it: `target_step`
    /// gives its charge and its error.
    fn target_run(&mut self, base: Out, keys: &[Key<'_>]) -> Res<(Out, usize)> {
        let Out::Ref(mut r) = base else {
            return Ok((base, 0));
        };
        let mut taken = Vec::new();
        let mut cur = self.store.at(&r);
        for key in keys {
            let Seen::Agg(a) = cur else { break };
            if !a.stored_ty().is_some_and(TyId::holds_handles) {
                break;
            }
            let Some((k, next)) = self.node_step(cur, key) else {
                break;
            };
            taken.push(k);
            cur = next;
        }
        for key in keys.iter().take(taken.len()) {
            if !matches!(key, Key::Index(..)) {
                self.charge(key_pos(key), 1)?;
            }
        }
        let count = taken.len();
        r.path.extend(taken);
        Ok((Out::Ref(r), count))
    }

    /// The text "`:=` target kind" of section 6.2 for the selected value `a`.
    pub(super) fn kind_text(a: &str) -> String {
        format!(
            "a `:=` target is a wire, a register, an own output, or a child input, not {a}; \
             select one of these, or assign a local with `=`"
        )
    }

    /// The step `key` of a target that starts at `start`, on the base `base`. An index step
    /// charged with its index.
    fn target_step(&mut self, start: Pos, base: Out, key: &Key<'_>) -> Res<Out> {
        if let (Seen::Handle(Handle::Inst { id, path, inst, .. }), Key::Field(q, f)) =
            (self.store.seen(&base), key)
        {
            let (id, path, inst) = (*id, *path, *inst);
            return self.child_port(start, *q, f, (id, path, inst));
        }
        let flagged = matches!(
            self.store.seen(&base),
            Seen::Agg(a) if a.stored_ty().is_some_and(TyId::holds_handles)
        );
        if !flagged {
            return fail(Code::S017, start, PART_TEXT.to_owned());
        }
        if !matches!(key, Key::Index(..)) {
            self.charge(key_pos(key), 1)?;
        }
        self.agg_key(base, key)
    }

    /// The input `f` of the child `inst` at `q`, with no charge. An output is `S017` at `start`.
    fn child_port(
        &self,
        start: Pos,
        q: Pos,
        f: &Ident,
        (id, path, inst): (usize, crate::names::PathId, usize),
    ) -> Res<Out> {
        let port = self
            .syms
            .fields
            .get(&f.id)
            .and_then(|s| self.elab.port(inst, (*s, None)));
        match port {
            Some(port) if port.input => Ok(Out::Made(Val::Handle(Handle::Input {
                inst: id,
                path,
                port,
            }))),
            Some(port) => fail(Code::S017, start, self.output_text(&port)),
            None => fail(
                Code::S010,
                q,
                format!("the instance has no port `{}`", f.name),
            ),
        }
    }

    /// The `S017` text "Child output as a `:=` target" of section 6.2, for the output `port`. An
    /// entry is named with its key, for example `req[3]`.
    fn output_text(&self, port: &crate::hw::Port) -> String {
        format!(
            "`{}` is an output of the child, not a target; the child drives its outputs, so bind \
             an input of the child",
            self.port_text(port)
        )
    }

    /// The entry of the family `f` of the child behind the `Instance` handle `cur`, with the
    /// static key `fk` at `xp`, in a `:=` target that starts at `start` (section 5.2). The key
    /// gets the type and range checks of a family selection. A key that the child did not declare
    /// is `S013` "Child family key". An input entry gives its handle, and an output entry is
    /// `S017`.
    fn child_target(
        &mut self,
        start: Pos,
        cur: &Out,
        f: &Ident,
        (xp, ko): (Pos, &Out),
    ) -> Res<Out> {
        let key = self.fam_key(self.store.value(ko)).key(xp)?;
        let Seen::Handle(Handle::Inst { id, path, inst, ty }) = self.store.seen(cur) else {
            return fail(Code::S017, start, PART_TEXT.to_owned());
        };
        let (id, path, inst, ty) = (*id, *path, *inst, *ty);
        let sym = self.port_sym(f).unwrap_or(0);
        match self.elab.port(inst, (sym, Some(key))) {
            Some(port) if port.input => Ok(Out::Made(Val::Handle(Handle::Input {
                inst: id,
                path,
                port,
            }))),
            Some(port) => fail(Code::S017, start, self.output_text(&port)),
            None => child_key(xp, &self.tys.text(ty), &f.name, key),
        }
    }
}
