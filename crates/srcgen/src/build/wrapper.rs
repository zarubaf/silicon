// SPDX-License-Identifier: Apache-2.0
//! The forwarding wrapper `W0` (front-end spec 9.3): a module that holds
//! one instance of the module after it and forwards each port of the
//! instance with a `comptime for` over `@ports` and `@field`.
//!
//! The wrapper has the signature of its child, so a parent binds and reads it
//! as it does the child, and a query of `@ports` sees the same list. The body
//! has the instance and the loop only, so each port of the wrapper comes from
//! the loop. The wrapper stands last among the signatures and no draw of the
//! main tape sees it: a parent of its child can name it in the place of the
//! child, which the query tape decides, so a program with no wrapper is the
//! program of the other tapes alone. The child takes each context of the
//! wrapper, with the arguments of the wrapper as its own. The twin writes the
//! ports out.

use super::portinfo::rows;
use super::reflect::RTy;
use super::{Builder, Built, Sig};
use crate::eval::Fault;
use crate::program::{FwdPort, SExpr, Stmt};

/// A program with queries has a wrapper in this many.
const WRAP_ODDS: u32 = 3;

impl Builder {
    /// The number of modules that the main tape sees: the wrapper comes
    /// last and is no choice of the main tape.
    pub(super) fn modules(&self) -> usize {
        self.sigs.iter().filter(|s| s.wraps.is_none()).count()
    }

    /// The wrapper of the module `j` at the end of the signatures, if the
    /// program has one and the query tape puts it in the place of `j`.
    pub(super) fn wrapper_of(&mut self, j: usize) -> Option<usize> {
        let w = self.sigs.iter().position(|s| s.wraps == Some(j))?;
        self.on_query(|b| b.tape.flag()).then_some(w)
    }

    /// The wrapper of one module, after the other modules. A program holds at
    /// most one, and a parent of the module can name it in its place.
    pub(super) fn wrapper(&mut self) {
        if !self.query_on || self.sigs.len() < 2 {
            return;
        }
        self.on_query(|b| {
            if b.tape.below(WRAP_ODDS) != 0 {
                return;
            }
            let j = 1 + b.tape.index(b.sigs.len() - 1);
            let Some(child) = b.sigs.get(j).cloned() else {
                return;
            };
            b.sigs.push(Sig {
                name: "W0".to_owned(),
                wraps: Some(j),
                ..child
            });
        });
    }

    /// The body of the wrapper `k`: the instance of the module that it
    /// wraps, and the loop. Each parent that named the wrapper gave the module
    /// the contexts, so the module has them.
    pub(super) fn wrapper_body(&mut self, k: usize, sig: &Sig) -> Built {
        let j = sig.wraps.ok_or(Fault::Type)?;
        let child = self.sigs.get(j).cloned().ok_or(Fault::Type)?;
        let args = sig
            .params
            .iter()
            .map(|(n, _)| SExpr::Name(n.clone()))
            .collect();
        // The arguments are the parameters of the wrapper, which are those of
        // the child, so the types of the ports hold as they are.
        let ports = rows(&child, &self.port_helpers, RTy::of)
            .into_iter()
            .map(|r| FwdPort {
                public: r.public,
                output: !r.input,
                ty: r.plan_ty,
            })
            .collect();
        let body = vec![
            Stmt::Instance("u0".to_owned(), child.name, args),
            Stmt::Forward {
                inst: "u0".to_owned(),
                ports,
            },
        ];
        *self.bodies.get_mut(k).ok_or(Fault::Type)? = Some(body);
        Ok(())
    }
}
