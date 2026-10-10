//! The size of the stack of the evaluator. The evaluator recurses over the AST, and each
//! active call or constant in progress starts the recursion again in its item. One pass
//! before the evaluation finds two heights: the highest node, and the highest node that
//! can start a nested evaluation, a call or the use of a constant. The evaluation runs a
//! group of nesting levels on each thread. A thread has room for the first height once and
//! for the second height at each level of its group.

use parse::ast::{Expr, Item, Stmt, TypeExpr};
use resolve::{Kind, Resolved, ResolvedExpr, Target};

/// The levels of stack of a group, for `parse::on_stack`, which gives each level the stack of
/// a level of the syntax depth.
const GROUP_LEVELS: u64 = 256;

/// The stack of the threads of an evaluation.
#[derive(Clone, Copy)]
pub(crate) struct Stack {
    /// The nesting levels that each thread runs.
    pub levels_per_thread: u64,
    /// The stack of each thread, in levels of `parse::on_stack`.
    pub thread_levels: usize,
}

/// The stack for the evaluation of `top` in the file scope of `file`.
pub(crate) fn of(file: &Resolved, top: &ResolvedExpr) -> Stack {
    let mut walk = Walk {
        file,
        top: Some(top),
        height: 0,
        nested: 0,
    };
    walk.expr(top.expr(), 1);
    walk.top = None;
    for item in file.ast() {
        walk.item(item);
    }
    let per_level = u64::try_from(walk.nested)
        .unwrap_or(u64::MAX)
        .saturating_add(2);
    let base = u64::try_from(walk.height)
        .unwrap_or(u64::MAX)
        .saturating_add(2);
    let levels_per_thread = (GROUP_LEVELS / per_level).max(1);
    let levels = levels_per_thread
        .saturating_mul(per_level)
        .saturating_add(base);
    Stack {
        levels_per_thread,
        thread_levels: usize::try_from(levels).unwrap_or(usize::MAX),
    }
}

struct Walk<'a> {
    file: &'a Resolved,
    /// The top expression while the walk is in it: it has its own map of targets.
    top: Option<&'a ResolvedExpr>,
    height: usize,
    nested: usize,
}

impl Walk<'_> {
    fn is_constant(&self, pos: parse::ast::Pos) -> bool {
        let target = match self.top {
            Some(top) => top.target(pos),
            None => self.file.target(pos),
        };
        matches!(target, Some(Target::Decl(id)) if self.file.decl(id).kind == Kind::Const)
    }

    fn reach(&mut self, depth: usize) {
        self.height = self.height.max(depth);
    }

    fn item(&mut self, item: &Item) {
        match item {
            Item::Const { ty, value, .. } => {
                self.ty(ty, 1);
                self.expr(value, 1);
            }
            Item::Fn {
                params, ret, body, ..
            } => {
                for p in params {
                    self.ty(&p.ty, 1);
                }
                self.ty(ret, 1);
                self.stmts(body, 1);
            }
            Item::Module { params, body, .. } => {
                for p in params {
                    self.ty(&p.ty, 1);
                }
                self.stmts(body, 1);
            }
        }
    }

    fn stmts(&mut self, ss: &[Stmt], depth: usize) {
        for s in ss {
            self.stmt(s, depth);
        }
    }

    fn stmt(&mut self, s: &Stmt, depth: usize) {
        self.reach(depth);
        let d = depth + 1;
        match s {
            Stmt::Local { ty, value, .. } => {
                if let Some(ty) = ty {
                    self.ty(ty, d);
                }
                self.expr(value, d);
            }
            Stmt::Assign { target, value, .. } | Stmt::Connect { target, value, .. } => {
                self.expr(target, d);
                self.expr(value, d);
            }
            Stmt::Reg { ty, init, .. } => {
                self.ty(ty, d);
                self.expr(init, d);
            }
            Stmt::Wire { ty, .. } | Stmt::Input { ty, .. } | Stmt::Output { ty, .. } => {
                self.ty(ty, d);
            }
            Stmt::Inst { args, .. } => {
                for a in args {
                    self.expr(a, d);
                }
            }
            Stmt::Ret { value, .. } => {
                if let Some(v) = value {
                    self.expr(v, d);
                }
            }
            Stmt::CtIf { cond, yes, no, .. } => {
                self.expr(cond, d);
                self.stmts(yes, d + 1);
                if let Some(no) = no {
                    self.stmts(no, d + 1);
                }
            }
            Stmt::CtFor { lo, hi, body, .. } => {
                self.expr(lo, d);
                self.expr(hi, d);
                self.stmts(body, d + 1);
            }
            Stmt::Block { body, .. } => self.stmts(body, d),
            Stmt::Expr { value, .. } => self.expr(value, d),
        }
    }

    fn ty(&mut self, t: &TypeExpr, depth: usize) {
        self.reach(depth);
        if let TypeExpr::Index { base, args, .. } = t {
            self.ty(base, depth + 1);
            for a in args {
                self.expr(a, depth + 1);
            }
        }
    }

    fn expr(&mut self, e: &Expr, depth: usize) {
        self.reach(depth);
        let d = depth + 1;
        match e {
            Expr::Num { .. } | Expr::Bool { .. } | Expr::Str { .. } => {}
            Expr::Name { pos, .. } => {
                if self.is_constant(*pos) {
                    self.nested = self.nested.max(depth);
                }
            }
            Expr::Unary { arg, .. } => self.expr(arg, d),
            Expr::Binary { lhs, rhs, .. } => {
                self.expr(lhs, d);
                self.expr(rhs, d);
            }
            Expr::Cond { cond, yes, no, .. } => {
                self.expr(cond, d);
                self.expr(yes, d);
                self.expr(no, d);
            }
            Expr::Call { callee, args, .. } => {
                self.nested = self.nested.max(depth);
                self.expr(callee, d);
                for a in args {
                    self.expr(a, d);
                }
            }
            Expr::Index { base, args, .. } => {
                self.expr(base, d);
                for a in args {
                    self.expr(a, d);
                }
            }
            Expr::Field { base, .. } => self.expr(base, d),
        }
    }
}
