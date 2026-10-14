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

use super::stat::Kind;
use super::{Builder, Ctx};
use crate::program::Stmt;

impl Builder {
    /// The next message `d<n>`. Each `diagnostic` has its own.
    pub(super) fn next_message(&mut self) -> String {
        let message = format!("d{}", self.messages);
        self.messages += 1;
        message
    }

    /// `diagnostic("dK", value);` of an `Int` or a `Bool` that holds in each
    /// env of the frame.
    pub(super) fn diagnostic(&mut self, ctx: &Ctx, out: &mut Vec<Stmt>) {
        let kind = if self.tape.below(3) == 2 {
            Kind::Bool
        } else {
            Kind::Int
        };
        let (value, _) = self.evaluated(kind, self.reach(ctx), &ctx.envs);
        note!(self, diagnostics);
        out.push(Stmt::Diagnostic(self.next_message(), value));
    }
}
