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

    /// Declares an item. If the name exists, returns the first declaration.
    pub(crate) fn declare_item(&mut self, name: &str, id: DeclId) -> Result<(), DeclId> {
        if let Some(&first) = self.items.get(name) {
            return Err(first);
        }
        self.items.insert(name.to_owned(), id);
        Ok(())
    }

    /// Declares a name in the innermost scope. A name of an outer scope is shadowed. If the
    /// scope has the name, returns the first declaration.
    pub(crate) fn declare_local(&mut self, name: &str, id: DeclId) -> Result<(), DeclId> {
        let level = self.opened.len();
        let stack = self.locals.entry(name.to_owned()).or_default();
        if let Some(&(first, at)) = stack.last()
            && at == level
        {
            return Err(first);
        }
        stack.push((id, level));
        if let Some(scope) = self.opened.last_mut() {
            scope.push(name.to_owned());
        }
        Ok(())
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
