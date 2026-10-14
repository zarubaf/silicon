// SPDX-License-Identifier: Apache-2.0
//! The cases of the memory block in `Silicon.Source.Test.Flatten` (section 7.6): the order of the
//! block, the compare of the valid bit, the extracts of a word, the write chain with its
//! temporaries, and the names. The text is the lowering of the Lean binary.

use crate::Budget;
use crate::tests_flatten::{elab_used, lowered, sil, sil_fuel, text, total};
use core_ir::text::print;

/// A memory `name` of the word type `w` and the depth `n`, with one read and one write. The
/// address has `a` bits, and `r` binds the response.
fn memory(name: &str, w: &str, n: u64, a: u32) -> String {
    format!(
        "module M() {{\n  input ra: UInt[{a}];\n  input re: Bool;\n  input wa: UInt[{a}];\n  \
         input wd: {w};\n  input we: Bool;\n  output v: Bool;\n  mem {name}: [{w}; {n}];\n  \
         let r = read_port({name}, ra, re);\n  write_port({name}, wa, wd, we);\n  \
         v := r.valid;\n}}\n"
    )
}

/// The lowered design before the canonical sort: the statements in the order of the lowering.
fn raw(src: &str, top: &str) -> String {
    match lowered(src, top, Budget::default().fuel) {
        Ok((_, l)) => print(&l.design),
        Err(e) => e,
    }
}

/// The lines of `s` that satisfy `keep`.
fn lines(s: &str, keep: impl Fn(&str) -> bool) -> Vec<String> {
    s.lines()
        .filter(|l| keep(l))
        .map(ToOwned::to_owned)
        .collect()
}

/// The ports and the domain of `memory`, in layout order.
fn ports(a: u32, w: u32) -> Vec<String> {
    vec![
        "    (input clock$0clk clock)".to_owned(),
        "    (input clock$0rst (bits 1))".to_owned(),
        format!("    (input ra (bits {a}))"),
        "    (input re (bits 1))".to_owned(),
        format!("    (input wa (bits {a}))"),
        format!("    (input wd (bits {w}))"),
        "    (input we (bits 1))".to_owned(),
        "    (output v (bits 1))".to_owned(),
    ]
}

/// The block of one memory in the order of the lowering. The memory comes first, then the two
/// response registers and the request `let` values. The two `next` statements and the write
/// come last. A depth of `2^A` has the `valid` bit `(const 1 1)`.
#[test]
fn the_block_of_a_memory_follows_section_7_6() {
    let mut want = vec!["(design M".to_owned(), "  (module M".to_owned()];
    want.extend(ports(2, 8));
    want.extend(
        [
            "    (mem m (bits 8) 4 clock$0clk)",
            "    (reg m$0rdata (bits 8) clock$0clk (reset sync clock$0rst (const 8 0)))",
            "    (reg m$0rvalid (bits 1) clock$0clk (reset sync clock$0rst (const 1 0)))",
            "    (let m$0ren (bits 1) re)",
            "    (let m$0raddr (bits 2) ra)",
            "    (next m$0rdata (mux m$0ren (read m m$0raddr) m$0rdata))",
            "    (next m$0rvalid (and m$0ren (const 1 1)))",
            "    (write m 0 wa wd (and we (xor clock$0rst (const 1 1))))",
            "    (let r$data (bits 8) (extract m$0rdata 0 8))",
            "    (let r$valid (bits 1) m$0rvalid)",
            "    (assign v r$valid)))",
        ]
        .map(ToOwned::to_owned),
    );
    assert_eq!(raw(&memory("m", "UInt[8]", 4, 2), "M"), text(&want));
}

/// The memories lower after the registers and before the named `let` values, in declaration
/// order.
#[test]
fn the_memories_lower_after_the_registers_and_before_the_lets() {
    let src = "module M() {\n  input a: UInt[1];\n  input e: Bool;\n  output y: Bool;\n  \
        reg q: Bool = false;\n  mem b: [Bool; 2];\n  mem a1: [Bool; 2];\n  \
        let x = b.read_port(a, e);\n  b.write_port(a, e, e);\n  \
        let z = a1.read_port(a, e);\n  a1.write_port(a, e, e);\n  \
        q := x.data;\n  y := z.valid;\n}\n";
    let heads = lines(&raw(src, "M"), |l| {
        l.starts_with("    (") && !l.starts_with("    (input") && !l.starts_with("    (output")
    });
    let heads: Vec<String> = heads
        .iter()
        .map(|l| {
            l.trim_start()
                .split(' ')
                .take(2)
                .collect::<Vec<_>>()
                .join(" ")
        })
        .collect();
    assert_eq!(
        heads,
        [
            "(reg q",
            "(mem b",
            "(reg b$0rdata",
            "(reg b$0rvalid",
            "(let b$0ren",
            "(let b$0raddr",
            "(next b$0rdata",
            "(next b$0rvalid",
            "(write b",
            "(mem a1",
            "(reg a1$0rdata",
            "(reg a1$0rvalid",
            "(let a1$0ren",
            "(let a1$0raddr",
            "(next a1$0rdata",
            "(next a1$0rvalid",
            "(write a1",
            "(let x$data",
            "(let x$valid",
            "(let z$data",
            "(let z$valid",
            "(next q",
            "(assign y"
        ]
    );
}

/// A depth that is not `2^A`, such as 3, 1, or 5, compares the read address with the depth.
#[test]
fn a_depth_that_is_no_power_of_two_compares_the_read_address() {
    let has = |n: u64, a: u32, row: &str| {
        let s = sil(&memory("m", "UInt[8]", n, a), "M");
        assert!(s.lines().any(|l| l == row), "{n}: {s}");
    };
    has(
        3,
        2,
        "    (next m$0rvalid (and m$0ren (icmp ult m$0raddr (const 2 3))))",
    );
    has(
        1,
        1,
        "    (next m$0rvalid (and m$0ren (icmp ult m$0raddr (const 1 1))))",
    );
    has(2, 1, "    (next m$0rvalid (and m$0ren (const 1 1)))");
    has(
        5,
        3,
        "    (next m$0rvalid (and m$0ren (icmp ult m$0raddr (const 3 5))))",
    );
}

/// A word of a record: each leaf is an `extract` at the sum of the widths of the earlier leaves.
/// The write data is the `concat` chain with the first leaf in the least significant bits. A
/// second `read_port` is `S018` at the call.
#[test]
fn a_record_word_extracts_each_leaf_at_its_offset() {
    let src = "struct W { a: UInt[3], b: Bool, c: SInt[4] }\n\
        module M() {\n  input ra: UInt[2];\n  input re: Bool;\n  input wd: W;\n  \
        output o: W;\n  output q: SInt[4];\n  mem m: [W; 3];\n  \
        let r = m.read_port(ra, re);\n  m.write_port(ra, wd, re);\n  \
        o := r.data;\n  q := m.read_port(ra, re).data.c;\n}\n";
    assert_eq!(sil(src, "M"), "S018 12:8");
    let src = src.replace("m.read_port(ra, re).data.c", "r.data.c");
    let s = sil(&src, "M");
    assert_eq!(
        lines(&s, |l| l.contains("extract") || l.contains("(write")),
        [
            "    (let r$data$a (bits 3) (extract m$0rdata 0 3))",
            "    (let r$data$b (bits 1) (extract m$0rdata 3 1))",
            "    (let r$data$c (bits 4) (extract m$0rdata 4 4))",
            "    (write m 0 ra (concat wd$c (concat wd$b wd$a)) (and re (xor clock$0rst (const 1 1))))"
        ]
    );
}

/// An array word: the element `k` is at the offset `k * w`. A static leaf of the data is a
/// constant.
#[test]
fn an_array_word_extracts_the_element_at_k_times_its_width() {
    let src = "module M() {\n  input a: UInt[2];\n  input x: UInt[5];\n  output q: UInt[5];\n  \
        mem m: [[UInt[5]; 3]; 4];\n  let r = m.read_port(a, true);\n  \
        m.write_port(a, [x, 7, x], true);\n  q := r.data[2];\n}\n";
    let s = sil(src, "M");
    assert_eq!(
        lines(&s, |l| l.contains("extract")
            || l.contains("(write")
            || (l.contains("$0r") && l.starts_with("    (let"))),
        [
            "    (let m$0raddr (bits 2) a)",
            "    (let m$0ren (bits 1) (const 1 1))",
            "    (let r$data$0e (bits 5) (extract m$0rdata 0 5))",
            "    (let r$data$1e (bits 5) (extract m$0rdata 5 5))",
            "    (let r$data$2e (bits 5) (extract m$0rdata 10 5))",
            "    (let r$valid (bits 1) m$0rvalid)",
            "    (write m 0 a (concat x (concat (const 5 7) x)) (and (const 1 1) (xor clock$0rst (const 1 1))))"
        ]
    );
}

/// The chain of the leaves `x$<lo>e` to `x$<hi>e` over `base`.
fn cat(lo: u64, hi: u64, base: &str) -> String {
    (lo..=hi).fold(base.to_owned(), |e, i| format!("(concat x${i}e {e})"))
}

/// The shift `a >> (c +% c)` with the temporary `t` for its count.
fn shift_by(t: &str) -> String {
    format!("(mux (icmp uge {t} (const 8 3)) (const 3 0) (shru a (extract {t} 0 3)))")
}

/// A word of 200 leaves: the spine of the write data binds `m$<k>t` each time it reaches the
/// height 64. The first temporary holds the leaves 0 to 63, and each later one holds 63 more
/// leaves and the earlier temporary. The temporaries of the address come first, and those of the
/// enable last.
#[test]
fn the_write_chain_of_a_wide_word_binds_its_spine_at_the_height_64() {
    let src = "module M() {\n  input x: [Bool; 200];\n  input a: UInt[3];\n  input c: UInt[8];\n  \
        output v: Bool;\n  mem m: [[Bool; 200]; 8];\n  \
        let r = m.read_port(a >> (c +% c), true);\n  \
        m.write_port(a >> (c +% c), x, (a >> (c +% c)) == a);\n  v := r.valid;\n}\n";
    let s = sil(src, "M");
    let keep = |l: &str| {
        l.starts_with("    (write")
            || l.starts_with("    (let m$0raddr")
            || ["0", "1", "2", "3", "4"]
                .iter()
                .any(|k| l.starts_with(&format!("    (let m${k}t")))
    };
    assert_eq!(
        lines(&s, keep),
        [
            format!("    (let m$0raddr (bits 3) {})", shift_by("m$0raddr$0t")),
            "    (let m$0raddr$0t (bits 8) (add c c))".to_owned(),
            "    (let m$0t (bits 8) (add c c))".to_owned(),
            format!("    (let m$1t (bits 64) {})", cat(1, 63, "x$0e")),
            format!("    (let m$2t (bits 127) {})", cat(64, 126, "m$1t")),
            format!("    (let m$3t (bits 190) {})", cat(127, 189, "m$2t")),
            "    (let m$4t (bits 8) (add c c))".to_owned(),
            format!(
                "    (write m 0 {} {} (and (icmp eq {} a) (xor clock$0rst (const 1 1))))",
                shift_by("m$0t"),
                cat(190, 199, "m$3t"),
                shift_by("m$4t")
            ),
        ]
    );
}

/// A user name alone that equals a core keyword gets the field `0k`, and its role names do not.
/// The source keyword `mem` cannot name a memory.
#[test]
fn a_memory_named_as_a_core_keyword_gets_the_field_0k_alone() {
    let s = sil(&memory("add", "UInt[8]", 4, 2), "M");
    assert_eq!(
        lines(&s, |l| l.starts_with("    (mem")
            || l.starts_with("    (next")
            || l.starts_with("    (write")),
        [
            "    (mem add$0k (bits 8) 4 clock$0clk)",
            "    (next add$0rdata (mux add$0ren (read add$0k add$0raddr) add$0rdata))",
            "    (next add$0rvalid (and add$0ren (const 1 1)))",
            "    (write add$0k 0 wa wd (and we (xor clock$0rst (const 1 1))))"
        ]
    );
    let s = sil(&memory("read", "UInt[8]", 4, 2), "M");
    assert_eq!(
        lines(&s, |l| l.starts_with("    (mem")
            || l.starts_with("    (reg")),
        [
            "    (reg read$0rdata (bits 8) clock$0clk (reset sync clock$0rst (const 8 0)))",
            "    (reg read$0rvalid (bits 1) clock$0clk (reset sync clock$0rst (const 1 0)))",
            "    (mem read$0k (bits 8) 4 clock$0clk)"
        ]
    );
    assert_eq!(sil(&memory("mem", "UInt[8]", 4, 2), "M"), "S001 8:7");
}

/// The lowering of `memory` with the depth 4 charges 245 units. The module charges 2, the domain
/// 20, the ports 17, and the block 164. The response lets charge 31, the binding 9, and the
/// design 2. A fuel one unit below the total gives `S015` at the top selection.
#[test]
fn the_lowering_of_a_small_memory_charges_245_units() {
    let src = memory("m", "UInt[8]", 4, 2);
    assert_eq!(total(&src, "M") - elab_used(&src, "M"), 245);
    assert_eq!(sil_fuel(&src, "M", total(&src, "M") - 1), "S015 1:1");
}

/// A `:=` binding of a response word that no `let` named takes each leaf from the word with its
/// offset: the leaf of a record, and the leaves of an array of tuples.
#[test]
fn a_binding_of_a_word_reads_the_leaves_at_their_offsets() {
    let record = "struct W { a: UInt[3], b: Bool, c: SInt[4] }\n\
        module M() {\n    input ra: UInt[2];\n    input re: Bool;\n    input wd: W;\n    \
        output o: W;\n    mem m: [W; 3];\n    o := m.read_port(ra, re).data;\n    \
        m.write_port(ra, wd, re);\n}\n";
    assert_eq!(
        lines(&sil(record, "M"), |l| l.contains("(assign")
            || l.contains("(write")),
        [
            "    (write m 0 ra (concat wd$c (concat wd$b wd$a)) (and re (xor clock$0rst (const 1 1))))",
            "    (assign o$a (extract m$0rdata 0 3))",
            "    (assign o$b (extract m$0rdata 3 1))",
            "    (assign o$c (extract m$0rdata 4 4))))",
        ]
    );
    let nested = "module M() {\n    input a: UInt[2];\n    input e: Bool;\n    \
        output q: [(UInt[2], Bool); 2];\n    mem m: [[(UInt[2], Bool); 2]; 4];\n    \
        q := m.read_port(a, e).data;\n    m.write_port(a, q, e);\n}\n";
    assert_eq!(
        lines(&sil(nested, "M"), |l| l.contains("(assign")
            || l.contains("(write")),
        [
            "    (write m 0 a (concat q$1e$1e (concat q$1e$0e (concat q$0e$1e q$0e$0e))) (and e (xor clock$0rst (const 1 1))))",
            "    (assign q$0e$0e (extract m$0rdata 0 2))",
            "    (assign q$0e$1e (extract m$0rdata 2 1))",
            "    (assign q$1e$0e (extract m$0rdata 3 2))",
            "    (assign q$1e$1e (extract m$0rdata 5 1))))",
        ]
    );
}

/// A named response gives a `let` for each leaf of the word, and an output bound to those names
/// is a name and not an extract.
#[test]
fn a_named_response_binds_each_leaf_once() {
    let src = "struct W { a: UInt[3], b: Bool, c: SInt[4] }\n\
        module M() {\n    input ra: UInt[2];\n    input re: Bool;\n    input wd: W;\n    \
        output o: W;\n    output p: (Bool, SInt[4]);\n    mem m: [W; 3];\n    \
        let r = m.read_port(ra, re);\n    m.write_port(ra, wd, re);\n    o := r.data;\n    \
        p := (r.data.b, r.data.c);\n}\n";
    assert_eq!(
        lines(&sil(src, "M"), |l| l.contains("(assign")
            || l.starts_with("    (let r$")),
        [
            "    (let r$data$a (bits 3) (extract m$0rdata 0 3))",
            "    (let r$data$b (bits 1) (extract m$0rdata 3 1))",
            "    (let r$data$c (bits 4) (extract m$0rdata 4 4))",
            "    (let r$valid (bits 1) m$0rvalid)",
            "    (assign o$a r$data$a)",
            "    (assign o$b r$data$b)",
            "    (assign o$c r$data$c)",
            "    (assign p$0e r$data$b)",
            "    (assign p$1e r$data$c)))",
        ]
    );
}
