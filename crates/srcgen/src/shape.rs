// SPDX-License-Identifier: Apache-2.0
//! The grouping of the ports of a module into aggregate ports, and the
//! entry names of their leaves in a source vector (frontend spec 7.5).

use core_ir::ast::Dir;

/// The most ports in one group.
const MAX_GROUP: usize = 4;

/// The type of an aggregate port.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Kind {
    /// `(UInt[a], UInt[b])`
    Tuple,
    /// `[UInt[w]; n]`, with equal widths.
    Array,
    /// The generated struct `R<id>`, with one `comptime W: Nat` for the
    /// width of its first field if `param` is set.
    Record { id: usize, param: bool },
}

/// Adjacent core ports of one direction that source declares as one
/// aggregate port. The leaf `i` of the port is the core port
/// `members[i]`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Group {
    /// The source name of the port.
    pub name: String,
    pub dir: Dir,
    pub kind: Kind,
    /// The core ports with their widths, in leaf order.
    pub members: Vec<(String, u32)>,
}

/// The name of the struct item of the record `id`.
fn record_name(id: usize) -> String {
    format!("R{id}")
}

impl Group {
    fn uint(width: u32) -> String {
        format!("UInt[{width}]")
    }

    /// The width that all members share, if they do.
    fn common_width(&self) -> Option<u32> {
        let (_, first) = self.members.first()?;
        self.members
            .iter()
            .all(|(_, w)| w == first)
            .then_some(*first)
    }

    fn first_width(&self) -> u32 {
        self.members.first().map_or(1, |(_, w)| *w)
    }

    /// The source type of the port.
    pub fn ty(&self) -> String {
        match self.kind {
            Kind::Tuple => {
                let parts: Vec<String> = self.members.iter().map(|(_, w)| Self::uint(*w)).collect();
                format!("({})", parts.join(", "))
            }
            Kind::Array => format!(
                "[{}; {}]",
                Self::uint(self.common_width().unwrap_or(1)),
                self.members.len()
            ),
            Kind::Record { id, param: false } => record_name(id),
            Kind::Record { id, param: true } => {
                format!("{}[{}]", record_name(id), self.first_width())
            }
        }
    }

    /// The literal of the port with the source text `parts` of its leaves.
    pub fn literal(&self, parts: &[String]) -> String {
        let list = parts.join(", ");
        match self.kind {
            Kind::Tuple => format!("({list})"),
            Kind::Array => format!("[{list}]"),
            Kind::Record { id, param: false } => format!("{}({list})", record_name(id)),
            Kind::Record { id, param: true } => {
                format!("{}[{}]({list})", record_name(id), self.first_width())
            }
        }
    }

    /// The name of the struct item of a record port.
    pub fn struct_name(&self) -> Option<String> {
        match self.kind {
            Kind::Record { id, .. } => Some(record_name(id)),
            _ => None,
        }
    }

    /// The struct item of a record port.
    pub fn struct_item(&self) -> Option<String> {
        let Kind::Record { param, .. } = self.kind else {
            return None;
        };
        let name = self.struct_name()?;
        let head = if param {
            format!("struct {name}(comptime W: Nat) {{\n")
        } else {
            format!("struct {name} {{\n")
        };
        let fields: Vec<String> = self
            .members
            .iter()
            .enumerate()
            .map(|(i, (_, w))| {
                let ty = if param && i == 0 {
                    "UInt[W]".to_owned()
                } else {
                    Self::uint(*w)
                };
                format!("    f{i}: {ty},\n")
            })
            .collect();
        Some(format!("{head}{}}}\n", fields.concat()))
    }

    /// The source text that reads the leaf `i`, and its entry name in a
    /// source vector.
    fn leaf(&self, i: usize) -> (String, String) {
        let n = &self.name;
        match self.kind {
            Kind::Tuple => (format!("{n}.{i}"), format!("{n}.{i}")),
            Kind::Array => (format!("{n}[{i}]"), format!("{n}.{i}")),
            Kind::Record { .. } => (format!("{n}.f{i}"), format!("{n}.f{i}")),
        }
    }
}

/// The groups of one module. A port in no group is a scalar port with its
/// core name.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct Shape {
    pub groups: Vec<Group>,
}

impl Shape {
    /// The group of the core port `port` and its leaf position.
    pub fn group_of(&self, port: &str) -> Option<(&Group, usize)> {
        self.groups
            .iter()
            .find_map(|g| Some((g, g.members.iter().position(|(m, _)| m == port)?)))
    }

    /// The source text that reads the core port `port`.
    pub fn read(&self, port: &str) -> Option<String> {
        let (group, i) = self.group_of(port)?;
        Some(group.leaf(i).0)
    }

    /// The sort key and the entry name of the core port `port` in a source
    /// vector. The layout sorts by the source name of the port, and the
    /// leaves of a port follow in packing order.
    fn entry(&self, port: &str) -> ((String, usize), String) {
        match self.group_of(port) {
            Some((group, i)) => ((group.name.clone(), i), group.leaf(i).1),
            None => ((port.to_owned(), 0), port.to_owned()),
        }
    }

    /// The entries `(name, value)` for the core ports `ports` in the port
    /// layout.
    pub fn layout<'a>(
        &self,
        ports: impl IntoIterator<Item = (&'a str, String)>,
    ) -> Vec<(String, String)> {
        let mut keyed: Vec<_> = ports
            .into_iter()
            .map(|(port, value)| {
                let (key, name) = self.entry(port);
                (key, name, value)
            })
            .collect();
        keyed.sort_by(|a, b| a.0.cmp(&b.0));
        keyed.into_iter().map(|(_, n, v)| (n, v)).collect()
    }
}

/// The data ports of a module as `(name, direction, width)` in port order,
/// and the tape that chooses the groups. Choice 0 is a scalar port, so an
/// empty tape gives no group.
pub(super) fn draw(
    ports: &[(String, Dir, u32)],
    tape: &mut impl Iterator<Item = u32>,
    ids: &mut usize,
) -> Shape {
    let mut next = |n: usize| tape.next().unwrap_or(0) as usize % n;
    let mut groups = Vec::new();
    let mut at = 0;
    while at < ports.len() {
        let run = ports[at..]
            .iter()
            .take(MAX_GROUP)
            .take_while(|(_, dir, _)| *dir == ports[at].1)
            .count();
        if next(2) == 0 || run < 2 {
            at += 1;
            continue;
        }
        let kind = next(3);
        let mut size = 2 + next(run - 1);
        if kind == 1 {
            // An array needs equal widths.
            size = ports[at..at + size]
                .iter()
                .take_while(|(_, _, w)| *w == ports[at].2)
                .count();
            if size < 2 {
                at += 1;
                continue;
            }
        }
        let members: Vec<(String, u32)> = ports[at..at + size]
            .iter()
            .map(|(n, _, w)| (n.clone(), *w))
            .collect();
        let kind = match kind {
            0 => Kind::Tuple,
            1 => Kind::Array,
            _ => {
                let param = next(2) == 1;
                *ids += 1;
                Kind::Record {
                    id: *ids - 1,
                    param,
                }
            }
        };
        groups.push(Group {
            name: format!("g_{}", members[0].0),
            dir: ports[at].1,
            kind,
            members,
        });
        at += size;
    }
    Shape { groups }
}
