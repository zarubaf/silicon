// SPDX-License-Identifier: Apache-2.0
//! The builder of the green tree. It makes each node directly. The builder of `rowan` caches
//! its nodes and hashes a nested node again at each level, which costs time in the square of
//! the depth for a deep tree.

use rowan::{GreenNode, GreenToken, NodeOrToken, SyntaxKind};

type Child = NodeOrToken<GreenNode, GreenToken>;

/// A place in the children of the open node, where `start_node_at` can wrap what follows.
#[derive(Clone, Copy)]
pub(crate) struct Checkpoint(usize);

pub(crate) struct TreeBuilder {
    /// The open nodes with their children so far, the innermost last. The root is the first.
    open: Vec<(SyntaxKind, Vec<Child>)>,
}

impl TreeBuilder {
    /// A builder with the root node open.
    pub(crate) fn new(root: SyntaxKind) -> Self {
        TreeBuilder {
            open: vec![(root, Vec::new())],
        }
    }

    fn children(&mut self) -> &mut Vec<Child> {
        let (_, children) = self.open.last_mut().unwrap_or_else(|| unreachable!());
        children
    }

    pub(crate) fn token(&mut self, kind: SyntaxKind, text: &str) {
        self.children()
            .push(NodeOrToken::Token(GreenToken::new(kind, text)));
    }

    pub(crate) fn start_node(&mut self, kind: SyntaxKind) {
        self.open.push((kind, Vec::new()));
    }

    pub(crate) fn checkpoint(&mut self) -> Checkpoint {
        Checkpoint(self.children().len())
    }

    /// Opens a node that holds the children from the checkpoint on.
    pub(crate) fn start_node_at(&mut self, checkpoint: Checkpoint, kind: SyntaxKind) {
        let moved = self.children().split_off(checkpoint.0);
        self.open.push((kind, moved));
    }

    /// Closes the innermost node. The root closes only in `finish`.
    pub(crate) fn finish_node(&mut self) {
        if self.open.len() > 1
            && let Some((kind, children)) = self.open.pop()
        {
            let node = GreenNode::new(kind, children);
            self.children().push(NodeOrToken::Node(node));
        }
    }

    /// Closes the root and returns it.
    pub(crate) fn finish(mut self) -> GreenNode {
        while self.open.len() > 1 {
            self.finish_node();
        }
        let (kind, children) = self.open.pop().unwrap_or_else(|| unreachable!());
        GreenNode::new(kind, children)
    }
}

/// A finished green tree. `rowan` frees a node by recursion, so this wrapper frees the tree
/// from a work list, and a drop is safe on any stack.
#[cfg_attr(test, derive(Debug))]
pub(crate) struct Green(Option<GreenNode>);

impl Green {
    pub(crate) fn new(root: GreenNode) -> Self {
        Green(Some(root))
    }

    pub(crate) fn node(&self) -> &GreenNode {
        self.0.as_ref().unwrap_or_else(|| unreachable!())
    }
}

impl Drop for Green {
    fn drop(&mut self) {
        // Each child gets one more owner before its parent goes, so a parent frees only
        // itself and the children go one at a time from the list.
        let mut work: Vec<GreenNode> = self.0.take().into_iter().collect();
        while let Some(node) = work.pop() {
            for child in node.children() {
                if let NodeOrToken::Node(child) = child {
                    work.push(child.to_owned());
                }
            }
        }
    }
}
