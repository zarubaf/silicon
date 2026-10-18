// SPDX-License-Identifier: Apache-2.0
//! The part that a `:=` target selects (Lean `Elab.targetPart`, design sections 5.2 and 9.4). The
//! steps of the target run from the root outward, and the static type of each base decides. A
//! field of an `Instance` handle selects a child input with no charge. A container of a type with
//! the handle flag charges 1 for a step, then its index evaluates and gets the checks of an index.
//! Each other base, also another handle, is `S017` at the start of the target, before the charge
//! and before the index evaluates. The target is an identity, so it opens no window and charges
//! no held root.

use super::place::{Sel, chain};
use super::{Evaluator, Out, Res, fail, need};
use crate::Code;
use crate::hw::{Handle, Ref, Root, Seen, Val};
use parse::ast::{Expr, Ident, Pos};
use resolve::Target as Resolved;

/// The `S017` text "Part as a `:=` target" of section 6.2.
const PART_TEXT: &str = "a `:=` target is a whole resource, not a part of a value; bind the whole \
                         resource, for example `r := P(a, b);`";

impl Evaluator<'_> {
    /// The value that the `:=` target `e` selects. A local root is a reference to its slot. Another
    /// root has no slot, so it evaluates, and its value names it in the text of `S017`.
    pub(super) fn target_part(&mut self, e: &Expr) -> Res<Out> {
        let (root, steps) = chain(e).unwrap_or((e, Vec::new()));
        let local = match root {
            Expr::Name { id, .. } => match self.target(*id) {
                Some(Resolved::Decl(decl)) if self.store.slot(decl).is_some() => Some(decl),
                _ => None,
            },
            _ => None,
        };
        let mut cur = if let Some(decl) = local {
            Out::Ref(Ref {
                root: Root::Local(self.store.frame_index(), decl),
                path: Vec::new(),
            })
        } else {
            let out = self.eval(root)?;
            need(root, out)?
        };
        let mut done = 0;
        while done < steps.len() {
            let (out, taken) = self.target_run(cur, steps.get(done..).unwrap_or_default())?;
            cur = out;
            done += taken;
            if let Some(step) = steps.get(done) {
                cur = self.target_step(e.pos(), cur, step)?;
                done += 1;
            }
        }
        Ok(cur)
    }

    /// The longest run of steps of `steps` through containers of a type with the handle flag,
    /// from the reference `base`: the part where the run ends, and the number of steps taken. The
    /// type of each base decides its check, so the run reads no node while the indices evaluate.
    /// Their steps then walk the path of `base` from the root once (`followed`), and the path
    /// does not grow again at each step. The root is parked for the whole run, so an index that
    /// changes it cannot change what the steps select. A step that fails comes after the walk of
    /// the steps before it, as in the order of Lean. An index without a call has no effect that
    /// a later check could reorder, so only an index with a call ends a run.
    fn target_run(&mut self, base: Out, steps: &[Sel<'_>]) -> Res<(Out, usize)> {
        let Out::Ref(r) = &base else {
            return Ok((base, 0));
        };
        let Seen::Agg(a) = self.store.seen(&base) else {
            return Ok((base, 0));
        };
        let Some(mut ty) = a.stored_ty().filter(|t| t.holds_handles()) else {
            return Ok((base, 0));
        };
        let root = r.root;
        let local = matches!(root, Root::Local(..));
        let cursor = local.then(|| r.clone());
        let at = self.store.park(base);
        if let Some(r) = cursor {
            self.store.cursor(at, r, true);
        }
        let mut keyed = Vec::with_capacity(steps.len());
        let mut stop = None;
        for step in steps {
            // An index with a call can record a diagnostic or change a local, so the selections
            // before it must have walked and passed their checks first (Lean selects each part
            // before the next index evaluates). The run ends here and the step runs alone.
            if !keyed.is_empty()
                && matches!(step, Sel::Index(_, args) if self.call_args.has_call(args))
            {
                break;
            }
            if let Err(e) = self.charge(step.pos(), 1) {
                stop = Some(e);
                break;
            }
            let before = local.then(|| self.store.changes_of(root));
            let key = match self.key(step) {
                Ok(key) => key,
                Err(e) => {
                    stop = Some(e);
                    break;
                }
            };
            let next = self.held_step(Some(ty), &key);
            self.store.cursor_step(at, next.map(|(number, _)| number));
            keyed.push(key);
            if before.is_some_and(|b| self.store.changes_of(root) != b) {
                break;
            }
            match next.and_then(|(_, t)| t) {
                Some(t) if t.holds_handles() && !self.tys.get(t).is_handle() => ty = t,
                _ => break,
            }
        }
        let out = self.followed(at, &keyed)?.out;
        match stop {
            Some(e) => Err(e),
            None => Ok((out, keyed.len())),
        }
    }

    /// The text "`:=` target kind" of section 6.2 for the selected value `a`.
    pub(super) fn kind_text(a: &str) -> String {
        format!(
            "a `:=` target is a wire, a register, an own output, or a child input, not {a}; \
             select one of these, or assign a local with `=`"
        )
    }

    /// The step `sel` of a target that starts at `start`, on the base `base`.
    fn target_step(&mut self, start: Pos, base: Out, sel: &Sel<'_>) -> Res<Out> {
        if let (Seen::Handle(Handle::Inst { id, path, inst, .. }), Sel::Field(q, f)) =
            (self.store.seen(&base), sel)
        {
            let (id, path, inst) = (*id, *path, *inst);
            return self.child_port(start, *q, f, (id, path, inst));
        }
        let flagged = matches!(
            self.store.seen(&base),
            Seen::Agg(a) if a.stored_ty().is_some_and(crate::types::TyId::holds_handles)
        );
        if !flagged {
            return fail(Code::S017, start, PART_TEXT.to_owned());
        }
        self.charge(sel.pos(), 1)?;
        // The base waits while the index evaluates, so the index cannot change what it selects.
        let at = self.store.park(base);
        let key = self.key(sel);
        let base = self.store.resume_one(at);
        self.agg_key(base, &key?)
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
            .and_then(|s| self.elab.port(inst, *s));
        match port {
            Some(port) if port.input => Ok(Out::Made(Val::Handle(Handle::Input {
                inst: id,
                path,
                port,
            }))),
            Some(_) => fail(
                Code::S017,
                start,
                format!(
                    "`{}` is an output of the child, not a target; the child drives its outputs, \
                     so bind an input of the child",
                    f.name
                ),
            ),
            None => fail(
                Code::S010,
                q,
                format!("the instance has no port `{}`", f.name),
            ),
        }
    }
}
