// SPDX-License-Identifier: Apache-2.0
//! The public name of a port (front-end spec 5.6): the name that the parent,
//! the schema, and the source vectors use.

use std::fmt;

/// A scalar port `pin`, or an entry `req[3]` of a family. The derived order
/// is the port layout of spec 7.5: the basename by its bytes, then no key,
/// then the key as a number. One basename has one form, so the order of two
/// public names of one module is total.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Public {
    pub(crate) base: String,
    pub(crate) key: Option<u32>,
}

impl Public {
    pub(crate) fn scalar(base: &str) -> Public {
        Public {
            base: base.to_owned(),
            key: None,
        }
    }
}

impl fmt::Display for Public {
    /// The name of the vector entry: `pin` or `req[3]`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.key {
            Some(k) => write!(f, "{}[{k}]", self.base),
            None => f.write_str(&self.base),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn entry(base: &str, key: u32) -> Public {
        Public {
            base: base.to_owned(),
            key: Some(key),
        }
    }

    #[test]
    fn keys_sort_as_numbers_and_after_the_bare_name() {
        let mut names = [
            entry("req", 10),
            entry("req", 2),
            Public::scalar("req"),
            Public::scalar("a"),
            entry("req", 0),
        ];
        names.sort();
        let text: Vec<String> = names.iter().map(Public::to_string).collect();
        assert_eq!(text, ["a", "req", "req[0]", "req[2]", "req[10]"]);
    }

    #[test]
    fn basenames_sort_by_bytes() {
        let mut names = [
            Public::scalar("a1"),
            Public::scalar("B"),
            Public::scalar("a"),
        ];
        names.sort();
        let text: Vec<String> = names.iter().map(Public::to_string).collect();
        assert_eq!(text, ["B", "a", "a1"]);
    }
}
