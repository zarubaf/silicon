// SPDX-License-Identifier: Apache-2.0
//! The part that a `:=` target selects (Lean `Elab.targetPart`, design sections 5.2 and 9.4). As in
//! a place, the indices come first, and one walk from the root then selects. A root that is not a
//! local evaluates first. Each index step charges 1, evaluates its index, and gets the static
//! check. A local root gives its live value after them. The walk then runs the steps from the
//! root outward, and the static type of each base decides. A base that is not an `Instance`
//! handle and has no handle flag is `S017` at the start of the target. A field of an `Instance`
//! handle selects a child input with no charge. A field and a selector `.N` of a container of a
//! type with the handle flag charge 1, then the step gets the checks of a selection. The target
//! is an identity, so it opens no window and charges no held root.

use super::place::{Key, Sel, chain, key_pos};
use super::{Evaluator, Out, Res, fail, need};
use crate::Code;
use crate::hw::{Handle, Ref, Root, Seen, Val};
use crate::types::TyId;
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
        let start = if let Some(decl) = local {
            Err(decl)
        } else {
            let out = self.eval(root)?;
            Ok(need(root, out)?)
        };
        let mut keys = Vec::with_capacity(steps.len());
        for step in &steps {
            if matches!(step, Sel::Index(..)) {
                self.charge(step.pos(), 1)?;
            }
            keys.push(self.key(step)?);
        }
        let mut cur = match start {
            Ok(out) => out,
            Err(decl) => Out::Ref(Ref {
                root: Root::Local(self.store.frame_index(), decl),
                path: Vec::new(),
            }),
        };
        let mut rest = keys.as_slice();
        while let Some(key) = rest.first() {
            let (out, taken) = self.target_run(cur, rest)?;
            cur = out;
            rest = rest.get(taken..).unwrap_or_default();
            if taken == 0 {
                cur = self.target_step(e.pos(), cur, key)?;
                rest = rest.get(1..).unwrap_or_default();
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
