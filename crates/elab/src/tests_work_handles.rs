// SPDX-License-Identifier: Apache-2.0
//! The work of the handle types and `read`, as the work bound of design section 5.5 states it for
//! the Rust front end (issue #277). Each family runs at a size `n` and at `2n`. The work is the
//! sum of all counters of the run. A doubled size must give at most twice the work, and the work
//! must stay within a constant times the fuel that the run used. The tests count the steps of the
//! walks and not the time.

use crate::counters::{Counts, last};
use crate::tests_elab::load;
use crate::{Abort, Budget, elaborate};
use std::fmt::Write;

/// A run: its counts, the units that it used, and its first error.
pub(crate) struct Run {
    pub(crate) counts: Counts,
    pub(crate) used: u64,
    pub(crate) error: Option<(String, String)>,
}

/// The run of the module `M` in `src` with the depth limit `depth`. The key makes the fuel
/// budget unique, and the counts of the run are keyed by it.
pub(crate) fn run(key: u64, depth: u64, src: &str) -> Run {
    run_with(920_000_000 + key, depth, src)
}

/// The run of the module `M` in `src` with the fuel `fuel` and the depth limit `depth`. The
/// counts of the run are keyed by the fuel, so a test that sweeps the fuel needs fuels that no
/// other test uses.
pub(crate) fn run_with(fuel: u64, depth: u64, src: &str) -> Run {
    let file = load(src).unwrap();
    let budget = Budget { fuel, depth };
    match elaborate(&file, "M", parse::DEFAULT_SYNTAX_DEPTH, budget) {
        Ok(Ok(design)) => Run {
            counts: last(),
            used: design.used(),
            error: None,
        },
        Ok(Err(e)) => Run {
            counts: last(),
            used: 0,
            error: Some((e.code.to_string(), e.message)),
        },
        Err(Abort::Usage(m)) => panic!("{m}"),
        Err(Abort::Stack(e)) => panic!("{e}"),
    }
}

/// The work of a run that must pass.
pub(crate) fn passing(key: u64, depth: u64, src: &str) -> Run {
    let r = run(key, depth, src);
    assert_eq!(r.error, None, "{src}");
    r
}

/// The doubled size gives at most twice the work, and more than the work at the size `n`.
pub(crate) fn doubles(n: &Run, twice: &Run) {
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

/// W1. Typed lets at `Reg[T]`, where `T` is an alias of a tuple of `m` elements. A typed use at a
/// handle type compares two ids and walks no type, so the work of one more `let` does not depend
/// on `m`.
#[test]
fn w1_a_typed_let_at_a_handle_type_walks_no_type() {
    let at = |m: usize, lets: usize, key: u64| {
        let mut src = "module M() {\n    input x: UInt[8];\n    type T = (\n".to_owned();
        src.push_str(&"        UInt[8],\n".repeat(m));
        src.push_str("    );\n    reg r: T = T();\n    r := T();\n");
        for k in 0..lets {
            writeln!(src, "    let a{k}: Reg[T] = r;").unwrap();
        }
        src.push_str("}\n");
        passing(key, 1000, &src).counts.total()
    };
    let slope = |m: usize, key: u64| (at(m, 128, key + 1) - at(m, 64, key)) / 64;
    let (small, large) = (slope(64, 30), slope(512, 40));
    assert_eq!(
        small, large,
        "the work of a let follows the size of the tuple"
    );
    assert!(small <= 40, "{small}");
    let (a, b) = (at(512, 64, 50), at(512, 128, 51));
    assert!(a < b && b <= 2 * a, "{a} {b}");
}

/// W4. An `S010` typed use with a type of `n` parts in its text. The text stops after 1024 bytes,
/// so the walk of the text visits a number of pieces that does not follow `n`.
#[test]
fn w4_the_text_of_a_huge_type_in_a_message_is_bounded() {
    let at = |n: usize, key: u64| {
        let src = format!(
            "struct S(comptime A: [UInt[8]; {n}]) {{}}\nmodule M() {{\n    reg r: UInt[8] = 0;\n    \
             r := 0;\n    let a: Reg[UInt[8]] = S[[UInt[8]; {n}]()]();\n}}\n"
        );
        let r = run(key, 1000, &src);
        let (code, message) = r.error.clone().unwrap_or_default();
        assert_eq!(code, "S010");
        assert!(message.contains("..."), "{message}");
        (r.counts.texted, message.len())
    };
    let ((small, len), (large, same)) = (at(1 << 10, 60), at(1 << 14, 61));
    assert_eq!(len, same);
    assert!(small <= 1100 && large <= 1100, "{small} {large}");
    assert_eq!(small, large);
}

/// W7. An `instance` statement with wide arguments interns its type from the converted arguments
/// that the typed use already paid for. More statements give linear work.
#[test]
fn w7_the_type_of_an_instance_statement_costs_its_arguments() {
    let at = |k: usize, key: u64| {
        let mut src = "module C(comptime x: [Nat; 256]) domains() {\n    output o: Bool;\n    o := true;\n}\n"
            .to_owned();
        src.push_str("const X: [Nat; 256] = [\n");
        src.push_str(&"    0,\n".repeat(256));
        src.push_str("];\nmodule M() domains() {\n    output o: Bool;\n    o := true;\n");
        for i in 0..k {
            writeln!(src, "    instance u{i} = C(X);").unwrap();
        }
        src.push_str("}\n");
        passing(key, 1000, &src)
    };
    let (n, twice) = (at(16, 70), at(32, 71));
    doubles(&n, &twice);
    assert!(twice.counts.total() <= 6 * twice.used);
}

/// The run of the module `M` in `src` with the fuel budget `fuel`.
fn run_fuel(fuel: u64, depth: u64, src: &str) -> Run {
    let file = load(src).unwrap();
    let budget = Budget { fuel, depth };
    match elaborate(&file, "M", parse::DEFAULT_SYNTAX_DEPTH, budget) {
        Ok(Ok(design)) => Run {
            counts: last(),
            used: design.used(),
            error: None,
        },
        Ok(Err(e)) => Run {
            counts: last(),
            used: 0,
            error: Some((e.code.to_string(), e.message)),
        },
        Err(Abort::Usage(m)) => panic!("{m}"),
        Err(Abort::Stack(e)) => panic!("{e}"),
    }
}

/// W3. `k` bindings `let x = read(r)` of a register with `m` rows of 64 leaves. A binding
/// charges the zero size of the type before its leaves expand, so the work follows the fuel. A
/// doubled number of bindings gives at most twice the work, and a run with half of the fuel
/// stops with `S015` before it expands the leaves of the later bindings.
#[test]
fn w3_a_binding_of_a_read_expands_its_leaves_after_its_charge() {
    let source = |k: usize, m: usize| {
        let mut src = format!(
            "module M() {{\n    input x: [[UInt[8]; 64]; {m}];\n    output o: UInt[8];\n    \
             reg r: [[UInt[8]; 64]; {m}] = [[UInt[8]; 64]; {m}]();\n    r := x;\n"
        );
        for i in 0..k {
            writeln!(src, "    let q{i} = read(r);").unwrap();
        }
        src.push_str("    o := read(r)[0][0];\n}\n");
        src
    };
    let (n, twice) = (
        passing(80, 1000, &source(8, 8)),
        passing(81, 1000, &source(16, 8)),
    );
    doubles(&n, &twice);
    assert!(twice.counts.total() <= 8 * twice.used);
    let wide = passing(82, 1000, &source(16, 16));
    assert!(wide.counts.total() <= 8 * wide.used);
    let half = run_fuel(wide.used / 2, 1000, &source(16, 16));
    assert_eq!(half.error.as_ref().map(|e| e.0.as_str()), Some("S015"));
    assert!(
        half.counts.total() <= 8 * (wide.used / 2),
        "{} {}",
        half.counts.total(),
        wide.used / 2
    );
}

/// The array of the `n` registers `r0` to `r{n-1}` of the data type `ty`, as a module body that
/// binds it to `rs` and `ss`.
fn registers(n: usize, ty: &str) -> String {
    let mut src = String::new();
    for k in 0..n {
        writeln!(src, "    reg r{k}: {ty} = {ty}();\n    r{k} := {ty}();").unwrap();
    }
    let list = (0..n)
        .map(|k| format!("r{k}"))
        .collect::<Vec<_>>()
        .join(", ");
    writeln!(src, "    let rs = [{list}];\n    let ss = [{list}];").unwrap();
    src
}

/// Issue #278, W1. The equality `rs == ss` of two arrays of `n` registers reads each leaf once,
/// after it charges the sizes. The work is linear in `n` and within a constant of the fuel.
#[test]
fn c1_the_equality_of_arrays_of_registers_reads_each_leaf_once() {
    let at = |n: usize, key: u64| {
        let mut src = "module M() {\n    output o: Bool;\n".to_owned();
        src.push_str(&registers(n, "UInt[8]"));
        src.push_str("    o := rs == ss;\n}\n");
        passing(key, 1000, &src)
    };
    let (n, twice) = (at(64, 100), at(128, 101));
    doubles(&n, &twice);
    assert!(twice.counts.total() <= 8 * twice.used);
}

/// Issue #278, W7. A data read of `k` registers of an aggregate type with the zero size `L`
/// charges `L` for each register, before it expands anything. A run with half of the fuel stops
/// with `S015` before the later reads, and its work stays within a constant of its fuel.
#[test]
fn c7_a_data_read_of_aggregate_registers_pays_each_zero_size_first() {
    let source = |k: usize| {
        let mut src = "module M() {\n    output o: Bool;\n".to_owned();
        src.push_str(&registers(k, "[UInt[8]; 64]"));
        src.push_str("    o := rs == ss;\n}\n");
        src
    };
    let (n, twice) = (
        passing(110, 1000, &source(16)),
        passing(111, 1000, &source(32)),
    );
    doubles(&n, &twice);
    assert!(twice.counts.total() <= 8 * twice.used);
    let half = run_fuel(twice.used / 2, 1000, &source(32));
    assert_eq!(half.error.as_ref().map(|e| e.0.as_str()), Some("S015"));
    assert!(
        half.counts.total() <= 8 * (twice.used / 2),
        "{} {}",
        half.counts.total(),
        twice.used / 2
    );
}

/// Issue #278, R16. A data read of `[[T; 0]; n]` makes the data type of the inner array once,
/// though `T` is a tuple of 4096 elements with a register. The charge of the read is the size of
/// the value, which does not follow `T`, so the work must not follow it either.
#[test]
fn c10_the_data_type_of_a_container_is_made_once() {
    let at = |n: usize, key: u64| {
        let mut src = "type T = (\n    Reg[UInt[8]],\n".to_owned();
        src.push_str(&"    UInt[8],\n".repeat(4095));
        src.push_str(
            ");\nmodule M() {\n    output o: Bool;\n    reg r: UInt[8] = 0;\n    r := 0;\n",
        );
        src.push_str("    let e: [T; 0] = [];\n");
        let list = vec!["e"; n].join(", ");
        writeln!(src, "    let xs = [{list}];\n    o := xs == xs;\n}}").unwrap();
        passing(key, 1000, &src)
    };
    let (n, twice) = (at(64, 120), at(128, 121));
    assert!(
        twice.counts.read < 4 * 128 + 4096 + 64,
        "{:?}",
        twice.counts
    );
    assert!(
        twice.counts.read - n.counts.read <= 8 * 64,
        "{} {}",
        n.counts.read,
        twice.counts.read
    );
}

/// Issue #278, W2. `k` calls that each pass an array of `n` registers to a formal of the same
/// type. Each call charges the copy of the array, and the typed use compares the type once, so the
/// work is linear in the copy charges.
#[test]
fn c2_calls_that_pass_an_array_of_handles_are_linear_in_their_copies() {
    let at = |n: usize, k: usize, key: u64| {
        let mut src = format!(
            "fn take(h: [Reg[UInt[8]]; {n}]) -> Nat {{\n    return 1;\n}}\nmodule M() {{\n    \
             output o: Bool;\n"
        );
        src.push_str(&registers(n, "UInt[8]"));
        for j in 0..k {
            writeln!(src, "    let c{j} = take(rs);").unwrap();
        }
        src.push_str("    o := true;\n}\n");
        passing(key, 1000, &src)
    };
    let (small, twice) = (at(32, 16, 130), at(32, 32, 131));
    doubles(&small, &twice);
    assert!(twice.counts.total() <= 8 * twice.used);
    let (wide, wider) = (at(32, 16, 132), at(64, 16, 133));
    doubles(&wide, &wider);
}

/// Issue #278, W6. The typed use of a tuple of `n` registers at `Reg[T]` leaves, where `T` is a
/// tuple of 4096 elements, compares two ids for each leaf and walks no type. The work of one more
/// leaf does not follow the size of `T`.
#[test]
fn c6_a_typed_use_at_handle_leaves_walks_no_type() {
    let at = |n: usize, key: u64| {
        let mut src = "type T = (\n".to_owned();
        src.push_str(&"    UInt[8],\n".repeat(4096));
        src.push_str(");\nmodule M() {\n    output o: Bool;\n    reg r: T = T();\n    r := T();\n");
        let leaves = vec!["Reg[T]"; n].join(", ");
        let regs = vec!["r"; n].join(", ");
        writeln!(
            src,
            "    let t: ({leaves}, UInt[8]) = ({regs}, 5);\n    o := true;\n}}"
        )
        .unwrap();
        passing(key, 1000, &src).counts.total()
    };
    let slope = |n: usize, key: u64| (at(2 * n, key + 1) - at(n, key)) / n as u64;
    let (small, large) = (slope(32, 140), slope(64, 150));
    assert_eq!(
        small, large,
        "the work of a leaf follows the work of the run"
    );
    assert!(small <= 60, "{small}");
}

/// Issue #278, W3. `n` pushes of a register and `n` pops of a list of handles. A `push` refreshes
/// the stored numbers by a delta, and a `pop` of an element of the element depth does too, so the
/// work is linear in `n`, and a rebuild of the list at each step would not be.
#[test]
fn c3_pushes_and_pops_of_handles_refresh_by_a_delta() {
    let at = |n: usize, key: u64| {
        let mut src =
            "module M() {\n    output o: Bool;\n    reg r: UInt[8] = 0;\n    r := 0;\n    \
                       let mut hs = list(Reg[UInt[8]]);\n"
                .to_owned();
        src.push_str(&"    hs.push(r);\n".repeat(n));
        for k in 0..n {
            writeln!(src, "    let p{k} = hs.pop();").unwrap();
        }
        src.push_str("    o := true;\n}\n");
        passing(key, 1000, &src)
    };
    let (n, twice) = (at(64, 160), at(128, 161));
    doubles(&n, &twice);
    assert!(twice.counts.total() <= 8 * twice.used);
}

/// Issue #278, W8. The write-back of a `List[List[Reg[T]]]` formal checks the depth of the value
/// from its stored numbers. A call charges the copy of the list, so the work of `k` calls is
/// within a constant of their fuel, and the work for each unit of the fuel of a call does not grow
/// with the length `m` of the list. A walk over the nodes for the depth would add work with no
/// fuel, and it would raise that ratio.
#[test]
fn c8_the_write_back_of_a_list_of_lists_reads_only_the_depth() {
    let at = |m: usize, k: usize, key: u64| {
        let mut src = "fn grow(mut l: List[List[Reg[UInt[8]]]], r: Reg[UInt[8]]) -> Nat {\n    \
                       l[0].push(r);\n    return 1;\n}\nmodule M() {\n    output o: Bool;\n    \
                       reg r: UInt[8] = 0;\n    r := 0;\n    \
                       let mut ll = list(List[Reg[UInt[8]]]);\n    ll.push(list(Reg[UInt[8]]));\n"
            .to_owned();
        src.push_str(&"    ll[0].push(r);\n".repeat(m));
        for j in 0..k {
            writeln!(src, "    let c{j} = grow(ll, r);").unwrap();
        }
        src.push_str("    o := true;\n}\n");
        passing(key, 1000, &src)
    };
    // The calls alone: the runs with `k` calls less the runs with none.
    let per_call = |m: usize, key: u64| {
        let (with, without) = (at(m, 8, key), at(m, 0, key + 1));
        let work = with.counts.total() - without.counts.total();
        let fuel = with.used - without.used;
        (work, fuel)
    };
    let (small, large) = (per_call(64, 170), per_call(128, 172));
    // A call does about half a unit of work for each unit of its fuel. A walk over the list adds
    // about one unit for each node of the copy, which pushes the ratio above three quarters.
    assert!(
        4 * small.0 <= 3 * small.1 && 4 * large.0 <= 3 * large.1,
        "the work and the fuel of the calls: {small:?} at 64, {large:?} at 128"
    );
}

/// Issue #278, W9. A `pop` of an element that is deeper than the element type charges the size of
/// the root and builds the list node again, in a list of tuples of a handle and a type. The work
/// of `p` such pops from a list of `k` elements stays within a constant of the fuel.
#[test]
fn c9_a_deep_pop_from_a_list_of_handle_tuples_is_paid_by_the_root_size() {
    let at = |k: usize, p: usize, key: u64| {
        let mut src = "type D = [[[UInt[8]; 2]; 2]; 2];\ntype E = (Reg[UInt[8]], Type);\n\
                       module M() {\n    output o: Bool;\n    reg r: UInt[8] = 0;\n    r := 0;\n    \
                       let mut hs = list(E);\n"
            .to_owned();
        src.push_str(&"    hs.push((r, D));\n".repeat(k));
        for j in 0..p {
            writeln!(src, "    let p{j} = hs.pop();").unwrap();
        }
        src.push_str("    o := true;\n}\n");
        passing(key, 1000, &src)
    };
    let (n, twice) = (at(32, 16, 180), at(32, 32, 181));
    assert!(
        n.counts.total() <= 8 * n.used,
        "{} {}",
        n.counts.total(),
        n.used
    );
    assert!(twice.counts.total() <= 8 * twice.used);
    let long = at(64, 16, 182);
    assert!(long.counts.total() <= 8 * long.used);
}

/// Issue #278, W4. A list of `n` handles as a module argument is `S011` from the flag of its type
/// and the kind of the value, so the check walks no element. The work of the statement does not
/// follow `n`: the difference of the runs with and without it is the same at both sizes.
#[test]
fn c4_a_container_of_handles_at_a_static_position_is_rejected_in_constant_work() {
    let build = |n: usize, last: &str| {
        format!(
            "module C(comptime p: List[Reg[UInt[8]]]) {{\n}}\nmodule M() {{\n    output o: Bool;\n    \
             reg r: UInt[8] = 0;\n    r := 0;\n    let mut hs = list(Reg[UInt[8]]);\n    \
             comptime for i in 0..{n} {{\n        hs.push(r);\n    }}\n    {last}\n}}\n"
        )
    };
    let extra = |n: usize, key: u64| {
        let rejected = run(key, 1000, &build(n, "instance u = C(hs);\n    o := true;"));
        assert_eq!(rejected.error.as_ref().map(|e| e.0.as_str()), Some("S011"));
        let accepted = passing(key + 1, 1000, &build(n, "o := true;"));
        rejected.counts.total().abs_diff(accepted.counts.total())
    };
    let (small, large) = (extra(1 << 10, 190), extra(1 << 12, 192));
    assert!(small <= 600 && large <= 600, "{small} {large}");
}

/// Issue #278, W5. `n` targets `rs[i] := e` through an array of registers. Each target charges 1
/// for its step and selects the register, so the work is linear in `n`.
#[test]
fn c5_targets_through_an_array_of_registers_are_linear() {
    let at = |n: usize, key: u64| {
        let mut src = "module M() {\n    input x: UInt[8];\n    output o: Bool;\n".to_owned();
        for k in 0..n {
            writeln!(src, "    reg r{k}: UInt[8] = 0;").unwrap();
        }
        let list = (0..n)
            .map(|k| format!("r{k}"))
            .collect::<Vec<_>>()
            .join(", ");
        writeln!(src, "    let rs = [{list}];").unwrap();
        for k in 0..n {
            writeln!(src, "    rs[{k}] := x;").unwrap();
        }
        src.push_str("    o := true;\n}\n");
        passing(key, 1000, &src)
    };
    let (n, twice) = (at(64, 200), at(128, 201));
    doubles(&n, &twice);
    assert!(twice.counts.total() <= 8 * twice.used);
}

/// Issue #278, review. The target `a[0]...[0] := x` through `d` nested containers of a register
/// steps along the path once for each level, so the work that the target adds is linear in the
/// depth `d`, and a walk of the grown path from the root at each level would be quadratic. The
/// containers are arrays, or lists that `push` builds. An index with a call (`z()`) changes
/// nothing, but a walk after each such index would be quadratic too.
#[test]
fn c11_a_deep_target_through_nested_containers_is_linear_in_its_depth() {
    let extra = |d: usize, lists: bool, call: bool, key: u64| {
        let build = |target: bool| {
            let mut src = "fn z() -> Nat {\n    return 0;\n}\nmodule M() {\n    input x: UInt[8];\n    output o: Bool;\n    \
                           reg r: UInt[8] = 0;\n"
                .to_owned();
            if lists {
                src.push_str("    let mut a0 = list(Reg[UInt[8]]);\n    a0.push(r);\n");
                for k in 1..d {
                    let elem = format!("{}Reg[UInt[8]]{}", "List[".repeat(k), "]".repeat(k));
                    writeln!(
                        src,
                        "    let mut a{k} = list({elem});\n    a{k}.push(a{});",
                        k - 1
                    )
                    .unwrap();
                }
                writeln!(src, "    let a = a{};", d - 1).unwrap();
            } else {
                writeln!(src, "    let a = {}r{};", "[".repeat(d), "]".repeat(d)).unwrap();
            }
            if target {
                let index = if call { "[z()]" } else { "[0]" };
                writeln!(src, "    a{} := x;", index.repeat(d)).unwrap();
            } else {
                src.push_str("    r := x;\n");
            }
            src.push_str("    o := true;\n}\n");
            src
        };
        let with = passing(key, 1000, &build(true));
        let without = passing(key + 1, 1000, &build(false));
        with.counts.total().abs_diff(without.counts.total())
    };
    for (lists, call, key) in [
        (false, false, 210),
        (true, false, 220),
        (false, true, 230),
        (true, true, 240),
    ] {
        let (n, twice) = (extra(32, lists, call, key), extra(64, lists, call, key + 2));
        assert!(
            n < twice && twice <= 2 * n + 64,
            "the work {n} at depth 32 and {twice} at depth 64 (lists: {lists}, calls: {call})"
        );
    }
}
