// SPDX-License-Identifier: Apache-2.0
//! One mutation of a typed program (front-end spec 11.4, mode 3).
//!
//! The mutation edits a copy of the items and prints it with the one
//! printer, so each mutant parses. The original program elaborates, and
//! each pass of the front ends stops the run (spec 6.2). A mutation that
//! adds one error of an early pass therefore fixes the first code, and
//! `Mutant::expect` predicts it:
//!
//! - A copy of a declaration is `S002` (pass 2): all local kinds and the
//!   items share one namespace in a scope, and the copy is in that scope.
//! - A name reference `q0` is `S003` (pass 3): `q` is no prefix of the
//!   builder, and the resolver checks each name, also in dead code.
//! - A deleted declaration that its item still mentions (an item: that
//!   any item still mentions) is `S003`. Generated names are unique in an
//!   item, so no other declaration catches the use.
//! - One argument more or less in a call of a named function is `S007`
//!   (pass 4), on all code. In a call through a function value, pass 5
//!   finds it when the call runs: `S007` where the site always runs (the
//!   top frame of a module, outside a lazy operand or branch), else no
//!   prediction. A `const` runs at its first use, so it predicts nothing.
//! - A deleted `:=` in the top frame of a module body is `S018` (pass 5):
//!   each module of a program has a context, so its top frame runs, and
//!   nothing else fails.
//!
//! - A `mut` actual whose root is no longer mutable is `S008` (pass 4) if
//!   a named function, `push`, or `pop` has the root as its `mut` actual.
//!   An assignment to the root gives no prediction, even with such a use.
//!   A `pop` of the receiver in the arguments of a receiver call on a list
//!   is `S008` (pass 4), on all code. In a call through a function value,
//!   pass 5 finds the window when the call runs: `S008` where the site
//!   always runs, else no prediction.
//!
//! - A call of a function that runs a `diagnostic`, or that writes back a
//!   `mut` actual of the module frame, in an arm of a hardware `if` or in
//!   a width is `S016` (pass 5, spec 9.4), where the site always runs. A
//!   hardware `if` evaluates both arms, but its condition must be a port
//!   or a register, or the negation of one: the front ends fold any other
//!   condition that is static by value, and that `if` takes one arm. A
//!   site in a branch, a loop, a lazy operand, or another item than a
//!   module body predicts nothing.
//!
//! Any other mutation can fail in pass 5 at a point that depends on the
//! values, or pass, so its prediction is `None`.

use super::program::{Item, Program, render_items};
use walk::Walk;

mod uses;
mod walk;

#[cfg(test)]
mod tests;

/// A mutant: its source text, what the mutation did, and the first code
/// that both front ends must report, where the pass order makes it certain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Mutant {
    pub text: String,
    pub what: String,
    pub expect: Option<&'static str>,
}

/// The kinds of mutation, in the cyclic order of the fallback.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    /// A statement of a module or helper body, or an item other than the
    /// top module, goes.
    Delete,
    /// A declaration statement or an item, copied right after itself.
    Duplicate,
    /// A name reference becomes `q0`.
    Rename,
    /// The last argument of an instance or a call goes.
    DropArg,
    /// An instance or a call gets the argument `0` at its end.
    AddArg,
    /// A width `w` becomes `(w + 1)`.
    Widen,
    /// A width becomes `0`.
    ZeroWidth,
    /// A static expression becomes `(1 / 0)`.
    Fault,
    /// The `let mut` root of a `mut` actual becomes `let`.
    Immutable,
    /// An argument of a receiver call on a list becomes `pop` of the list:
    /// the `pop` is in the window of the receiver.
    Window,
    /// The same, in a call through a function value.
    ValueWindow,
    /// A static operand in an arm becomes a call of a function that runs a
    /// `diagnostic`: a graph effect in an arm.
    ArmEffect,
    /// A width becomes a call of that function: a graph effect in a type.
    TypeEffect,
    /// A static operand in an arm becomes a call that takes a `let mut`
    /// static `Int` from before the arm as its `mut` actual: a write-back
    /// in an arm.
    ArmMutation,
    /// The same for a width.
    TypeMutation,
}

const KINDS: [Kind; 15] = [
    Kind::Delete,
    Kind::Duplicate,
    Kind::Rename,
    Kind::DropArg,
    Kind::AddArg,
    Kind::Widen,
    Kind::ZeroWidth,
    Kind::Fault,
    Kind::Immutable,
    Kind::Window,
    Kind::ValueWindow,
    Kind::ArmEffect,
    Kind::TypeEffect,
    Kind::ArmMutation,
    Kind::TypeMutation,
];

/// The name of the function that runs a `diagnostic`.
const EFFECT_FN: &str = "e0";

/// The name of the function with a `mut` formal that it never changes.
const KEEP_FN: &str = "p0";

impl Kind {
    /// The function that the mutant adds, with its newline.
    fn function(self) -> String {
        match self {
            Kind::ArmEffect | Kind::TypeEffect => format!(
                "comptime fn {EFFECT_FN}(x: Int) -> Int {{\n    diagnostic(\"{EFFECT_FN}\", x);\n    return x;\n}}\n"
            ),
            Kind::ArmMutation | Kind::TypeMutation => {
                format!("comptime fn {KEEP_FN}(mut n: Int, x: Int) -> Int {{\n    return x;\n}}\n")
            }
            _ => String::new(),
        }
    }
}

/// The mutant of `program` for the kind `kind % KINDS.len()`, or for the next kind
/// in cyclic order that has a site, at the site `site % count` in the
/// pre-order of the items.
#[must_use]
pub fn mutate(program: &Program, kind: u32, site: u32) -> Mutant {
    let first = kind as usize % KINDS.len();
    let mutant = KINDS
        .iter()
        .cycle()
        .skip(first)
        .take(KINDS.len())
        .find_map(|&kind| {
            let count = sites(kind, &program.items, &program.top);
            if count == 0 {
                return None;
            }
            let mut items = program.items.clone();
            let (what, expect) = apply(kind, &mut items, &program.top, site as usize % count)?;
            Some(Mutant {
                text: render_items(&items) + &kind.function(),
                what,
                expect,
            })
        });
    // A built program has the `:=` of a top output, a `Delete` site. The
    // equal text shows the bug to `diff-si`.
    mutant.unwrap_or_else(|| Mutant {
        text: program.text(),
        what: "no mutation site".to_owned(),
        expect: None,
    })
}

/// The number of sites of `kind` in `items`.
fn sites(kind: Kind, items: &[Item], top: &str) -> usize {
    let mut w = Walk::new(kind, top, None);
    w.items(&mut items.to_vec());
    w.seen
}

/// Applies `kind` at the site `site` and gives what it did and the
/// predicted code, or `None` if `site` is not below `sites`.
fn apply(
    kind: Kind,
    items: &mut Vec<Item>,
    top: &str,
    site: usize,
) -> Option<(String, Option<&'static str>)> {
    let mut w = Walk::new(kind, top, Some(site));
    w.items(items);
    let Hit { what, effect } = w.hit?;
    let expect = match effect {
        Effect::Code(c) => c,
        Effect::Gone(name, scope) => {
            let scope = match scope {
                Some(i) => items.get(i..=i).unwrap_or_default(),
                None => items.as_slice(),
            };
            mentions(&name, scope).then_some("S003")
        }
    };
    Some((what, expect))
}

/// Whether a name reference in `items` is `name`: a value, an assignment
/// target, the instance of a field, an instance module, or a callee. The
/// guard `x == 0` of a `comptime fn` is no walked expression, so neither
/// this check nor `Rename` sees it. That costs no prediction: the guard
/// names the first parameter, and no mutation deletes a parameter.
fn mentions(name: &str, items: &[Item]) -> bool {
    let mut w = Walk::new(Kind::Rename, "", None);
    w.items(&mut items.to_vec());
    w.names.iter().any(|n| n == name)
}

/// The effect of a mutation on the first error.
enum Effect {
    Code(Option<&'static str>),
    /// The declaration of a name went: `S003` if the item at the index
    /// (all items if `None`) still mentions it.
    Gone(String, Option<usize>),
}

struct Hit {
    what: String,
    effect: Effect,
}
