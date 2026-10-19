// SPDX-License-Identifier: Apache-2.0
//! How the statements after a `let mut` use its root (front-end spec 9.1).

use super::super::program::{HExpr, Stmt};

/// The mutations of one root.
#[derive(Default)]
pub(super) struct Uses {
    /// An assignment `root = e;`.
    assigned: bool,
    /// A `push`, a `pop`, or a call of a named function with the root as a
    /// `mut` actual. Pass 4 sees it.
    named: bool,
}

impl Uses {
    /// The first code of a program whose root is no longer mutable: pass 4
    /// reports a named `mut` actual (spec 9.1). An assignment to an
    /// immutable root has another code, and a call through a function value
    /// is seen only when it runs.
    pub(super) fn code(&self) -> Option<&'static str> {
        (self.named && !self.assigned).then_some("S008")
    }
}

/// The names of the helpers with a `mut` first formal, and of the function
/// values.
pub(super) struct Callees<'a> {
    pub(super) mut_helpers: &'a [String],
    pub(super) values: &'a [String],
}

/// The uses of `root` in `body`. Generated names are unique in an item, so
/// the statements after the declaration are the whole scope.
pub(super) fn of(root: &str, body: &[Stmt], callees: &Callees) -> Uses {
    let mut uses = Uses::default();
    stmts(root, body, callees, &mut uses);
    uses
}

fn stmts(root: &str, body: &[Stmt], callees: &Callees, uses: &mut Uses) {
    for s in body {
        match s {
            Stmt::Push(list, _) | Stmt::PopLet(_, list) => uses.named |= list == root,
            Stmt::MutCall {
                root: r,
                f,
                receiver,
                ..
            } => uses.named |= r == root && (*receiver || !callees.values.contains(f)),
            Stmt::Assign(n, v) => {
                uses.assigned |= n == root;
                hexpr(root, v, callees, uses);
            }
            Stmt::Let { value, .. } | Stmt::Connect(_, value) => hexpr(root, value, callees, uses),
            Stmt::If(_, then, els) => {
                stmts(root, then, callees, uses);
                if let Some(els) = els {
                    stmts(root, els, callees, uses);
                }
            }
            Stmt::For(_, _, _, body) | Stmt::Block(body) => stmts(root, body, callees, uses),
            _ => {}
        }
    }
}

fn hexpr(root: &str, e: &HExpr, callees: &Callees, uses: &mut Uses) {
    let is_root = |e: &HExpr| matches!(e, HExpr::Name(n) if n == root);
    match e {
        HExpr::Name(_) | HExpr::Field(..) | HExpr::Static(_) | HExpr::Make(..) | HExpr::Unit => {}
        HExpr::Unary(_, a) | HExpr::Resize(_, a) | HExpr::Reinterpret(_, a) => {
            hexpr(root, a, callees, uses);
        }
        HExpr::Binary(_, a, b) => {
            hexpr(root, a, callees, uses);
            hexpr(root, b, callees, uses);
        }
        HExpr::ReadPort { addr, en, .. } => {
            hexpr(root, addr, callees, uses);
            hexpr(root, en, callees, uses);
        }
        HExpr::If(c, t, f) => {
            for x in [c, t, f] {
                hexpr(root, x, callees, uses);
            }
        }
        HExpr::Match(m) => {
            hexpr(root, &m.scrutinee, callees, uses);
            for (_, a) in &m.arms {
                hexpr(root, a, callees, uses);
            }
        }
        HExpr::Ctor(_, _, args) => {
            for a in args {
                hexpr(root, a, callees, uses);
            }
        }
        HExpr::Call(f, args) => {
            uses.named |= args.first().is_some_and(is_root) && callees.mut_helpers.contains(f);
            for a in args {
                hexpr(root, a, callees, uses);
            }
        }
        HExpr::Receiver(recv, f, args) => {
            uses.named |= is_root(recv) && callees.mut_helpers.contains(f);
            hexpr(root, recv, callees, uses);
            for a in args {
                hexpr(root, a, callees, uses);
            }
        }
    }
}
