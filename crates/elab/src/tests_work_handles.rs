// SPDX-License-Identifier: Apache-2.0
//! The work of the handle types and `read`, as the work bound of design section 5.5 states it for
//! the Rust front end (issue #277). Each family runs at a size `n` and at `2n`. The work is the
//! sum of all counters of the run. A doubled size must give at most twice the work, and the work
//! must stay within a constant times the fuel that the run used. The tests count the steps of the
//! walks and not the time.

use crate::counters::{Counts, of};
use crate::tests_elab::load;
use crate::{Abort, Budget, elaborate};
use std::fmt::Write;

/// A run: its counts, the units that it used, and its first error.
struct Run {
    counts: Counts,
    used: u64,
    error: Option<(String, String)>,
}

/// The run of the module `M` in `src` with the depth limit `depth`. The key makes the fuel
/// budget unique, and the counts of the run are keyed by it.
fn run(key: u64, depth: u64, src: &str) -> Run {
    let fuel = 920_000_000 + key;
    let file = load(src).unwrap();
    let budget = Budget { fuel, depth };
    match elaborate(&file, "M", parse::DEFAULT_SYNTAX_DEPTH, budget) {
        Ok(Ok(design)) => Run {
            counts: of(fuel),
            used: design.used(),
            error: None,
        },
        Ok(Err(e)) => Run {
            counts: of(fuel),
            used: 0,
            error: Some((e.code.to_string(), e.message)),
        },
        Err(Abort::Usage(m)) => panic!("{m}"),
        Err(Abort::Stack(e)) => panic!("{e}"),
    }
}

/// The work of a run that must pass.
fn passing(key: u64, depth: u64, src: &str) -> Run {
    let r = run(key, depth, src);
    assert_eq!(r.error, None, "{src}");
    r
}

/// The doubled size gives at most twice the work, and more than the work at the size `n`.
fn doubles(n: &Run, twice: &Run) {
    let (a, b) = (n.counts.total(), twice.counts.total());
    assert!(a < b && b <= 2 * a, "the work {a} at n and {b} at 2n");
}

/// W2. `Instance[C, ...]` with `n` arguments of an array of 256 elements. Each argument charges
/// its size after its typed use, and the type interns its arguments once, so the work is linear
/// in the charged sizes.
#[test]
fn w2_an_instance_type_with_wide_arguments_is_linear() {
    let at = |n: usize, key: u64| {
        let mut src = "module C(\n".to_owned();
        for k in 0..n {
            writeln!(src, "    comptime x{k}: [Nat; 256],").unwrap();
        }
        src.push_str(") domains() {\n    output o: Bool;\n    o := true;\n}\n");
        src.push_str("const X: [Nat; 256] = [\n");
        src.push_str(&"    0,\n".repeat(256));
        src.push_str("];\nmodule M() domains() {\n    output o: Bool;\n    let a = [X];\n");
        src.push_str("    type H = Instance[C,\n");
        src.push_str(&"        a[0],\n".repeat(n));
        src.push_str("    ];\n    o := true;\n}\n");
        passing(key, 1000, &src)
    };
    let (n, twice) = (at(16, 1), at(32, 2));
    doubles(&n, &twice);
    assert!(twice.counts.total() <= 6 * twice.used);
}

/// W5. The serialization of a nested instance type as a module argument. Each level adds a
/// constant number of bytes, and the work follows the serialization charge.
#[test]
fn w5_the_serialization_of_a_nested_instance_type_follows_its_charge() {
    let at = |n: usize, key: u64| {
        let mut ty = "UInt[8]".to_owned();
        for _ in 0..n {
            ty = format!("Instance[C, {ty}]");
        }
        let src = format!(
            "module C(comptime t: Type) domains() {{\n    output o: Bool;\n    o := true;\n}}\n\
             module M() domains() {{\n    output o: Bool;\n    instance u = C({ty});\n    \
             o := u.o;\n}}\n"
        );
        passing(key, 1000, &src)
    };
    let (n, twice) = (at(32, 10), at(64, 11));
    doubles(&n, &twice);
    assert!(twice.counts.total() <= 8 * twice.used);
}

/// W6. `Mem[UInt[8], 1 << 2^20]` is `S012` with a bounded value in its text. The compare is by
/// bit length, so the work does not follow the size of the integer.
#[test]
fn w6_a_huge_memory_depth_is_rejected_by_its_bit_length() {
    let src = "module M() domains() {\n    output o: Bool;\n    type H = Mem[UInt[8], 1 << 1048576];\n    o := true;\n}\n";
    let r = run(20, 1000, src);
    assert_eq!(
        r.error,
        Some((
            "S012".to_owned(),
            "a memory depth is 1 to 16777216, not an integer of 1048577 bits; use a depth in \
             this range"
                .to_owned()
        ))
    );
    assert!(r.counts.total() < 1_000_000, "{:?}", r.counts);
}
