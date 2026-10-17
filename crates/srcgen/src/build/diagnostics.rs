// SPDX-License-Identifier: Apache-2.0
//! `diagnostic(message, value)` statements (front-end spec 8.2, 9.4).
//!
//! A call of `diagnostic` is a graph effect: in a width, a `const`, a struct
//! argument, a parameter type, or a hardware arm it is `S016`. A function
//! that runs one, directly, through a call, or through a function value, is
//! effectful, and so is a call of it. The builder makes two effectful
//! forms: the statement here, and a `comptime fn` with a `mut` formal whose
//! `diag` field is set (`mutcalls`). Their calls are statements of a module
//! body, where `Builder::static_mut_call` and `frame` put them, and no
//! expression builder names such a function: a value call has no `mut`
//! formal.

use super::stat::{self, Kind};
use super::{Builder, Ctx};
use crate::program::{SExpr, STy, Stmt};

impl Builder {
    /// The next message `d<n>`. Each `diagnostic` has its own.
    pub(super) fn next_message(&mut self) -> String {
        let message = format!("d{}", self.messages);
        self.messages += 1;
        message
    }

    /// `diagnostic("dK", value);` of a static value that holds in each env
    /// of the frame: an integer or a Boolean, a string, a container literal,
    /// or a name of any other static type (a list, a function, a finite
    /// integer). The record shows the serialization of the value (spec 7.1).
    pub(super) fn diagnostic(&mut self, ctx: &Ctx, out: &mut Vec<Stmt>) {
        let value = self.diagnostic_value(ctx);
        note!(self, diagnostics);
        out.push(Stmt::Diagnostic(self.next_message(), value));
    }

    fn diagnostic_value(&mut self, ctx: &Ctx) -> SExpr {
        let r = self.reach(ctx);
        let scalar = |b: &mut Builder, kind| b.evaluated(kind, r, &ctx.envs).0;
        // The names of each type that a literal does not make.
        let named = |is: fn(&STy) -> bool| -> Vec<&String> {
            ctx.statics
                .iter()
                .filter(|(_, t)| is(t))
                .map(|(n, _)| n)
                .collect()
        };
        if self.aside(5) {
            note!(self, enum_diagnostics);
            let packed = self.side_below(4) == 0;
            if self.side_below(3) == 0
                && let Some(m) = self.on_side(|b| b.finite_match(r))
            {
                return m;
            }
            if let Some((def, value)) = self.any_enum_value(r) {
                if packed {
                    note!(self, enum_bits);
                    return SExpr::Pack(def.name, Box::new(value));
                }
                return value;
            }
        }
        let candidate = match self.tape.below(12) {
            0..=2 => return scalar(self, Kind::Int),
            3 => return scalar(self, Kind::Bool),
            4 => self.sexpr(Kind::Str, stat::DEPTH, r),
            5 | 6 => {
                let ty = self.static_container_ty();
                self.container(&ty, stat::DEPTH, r)
            }
            7 => match self.record_ty() {
                Some(ty) => self.container(&ty, stat::DEPTH, r),
                None => return scalar(self, Kind::Int),
            },
            8 => {
                let finite = named(|t| matches!(t, STy::UInt(_) | STy::SInt(_)));
                if finite.is_empty() {
                    self.pick_name(&named(|t| matches!(t, STy::Fn(_))))
                } else {
                    self.pick_name(&finite)
                }
            }
            9 | 10 => {
                let lists = named(|t| matches!(t, STy::List(_)));
                if lists.is_empty() || self.tape.below(3) == 0 {
                    self.list_value(r).0
                } else {
                    self.pick_name(&lists)
                }
            }
            _ => self.pick_name(&named(|t| {
                !matches!(t, STy::Nat | STy::Int | STy::Bool | STy::Enum(_))
            })),
        };
        if self.values(&candidate, &ctx.envs).is_some() {
            note!(self, structured_diagnostics);
            return candidate;
        }
        scalar(self, Kind::Int)
    }

    /// One of `names`, or the literal `0` if there is none.
    fn pick_name(&mut self, names: &[&String]) -> SExpr {
        match names.get(self.tape.index(names.len())) {
            Some(n) => SExpr::Name((*n).clone()),
            None => stat::int(0),
        }
    }
}
