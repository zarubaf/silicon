// SPDX-License-Identifier: Apache-2.0
//! The item namespace and the stack of local scopes. A lookup is one map access, whatever
//! the nesting: each name keeps a stack of its bindings with the level of each.

use crate::DeclId;
use std::collections::BTreeMap;

#[derive(Default)]
pub(crate) struct Scopes {
    items: BTreeMap<String, DeclId>,
    /// For each name, its bindings in the open scopes, innermost last, with their levels.
    locals: BTreeMap<String, Vec<(DeclId, usize)>>,
    /// The names that each open scope declared, to remove them when it closes.
    opened: Vec<Vec<String>>,
}

impl Scopes {
    /// The scopes of the file scope: the items and no local.
    pub(crate) fn of_items(items: BTreeMap<String, DeclId>) -> Scopes {
        Scopes {
            items,
            ..Scopes::default()
        }
    }

    pub(crate) fn open(&mut self) {
        self.opened.push(Vec::new());
    }

    pub(crate) fn close(&mut self) {
        for name in self.opened.pop().unwrap_or_default() {
            if let Some(stack) = self.locals.get_mut(&name) {
                stack.pop();
                if stack.is_empty() {
                    self.locals.remove(&name);
                }
            }
        }
    }

    /// Declares an item. Returns false, and keeps the first declaration, if the name exists.
    pub(crate) fn declare_item(&mut self, name: &str, id: DeclId) -> bool {
        if self.items.contains_key(name) {
            return false;
        }
        self.items.insert(name.to_owned(), id);
        true
    }

    /// Declares a name in the innermost scope. A name of an outer scope is shadowed. If the
    /// scope has the name, returns false and keeps the first declaration.
    pub(crate) fn declare_local(&mut self, name: &str, id: DeclId) -> bool {
        let level = self.opened.len();
        let stack = self.locals.entry(name.to_owned()).or_default();
        if let Some(&(_, at)) = stack.last()
            && at == level
        {
            return false;
        }
        stack.push((id, level));
        if let Some(scope) = self.opened.last_mut() {
            scope.push(name.to_owned());
        }
        true
    }

    /// The item with the name, past each local.
    pub(crate) fn item(&self, name: &str) -> Option<DeclId> {
        self.items.get(name).copied()
    }

    /// The innermost local, else the item, with the name.
    pub(crate) fn lookup(&self, name: &str) -> Option<DeclId> {
        self.locals
            .get(name)
            .and_then(|stack| stack.last())
            .map(|&(id, _)| id)
            .or_else(|| self.items.get(name).copied())
    }

    pub(crate) fn into_items(self) -> BTreeMap<String, DeclId> {
        self.items
    }
}
