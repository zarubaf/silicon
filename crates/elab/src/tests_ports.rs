// SPDX-License-Identifier: Apache-2.0
//! The cases of the memory port calls in `Silicon.Source.Test.Elab` (section 6.2). The
//! elaboration alone runs them, so the units are those of Lean `Elab.elaborate`. A call gives
//! each error at the call, and a receiver call starts at its receiver.

use crate::Budget;
use crate::agg::Agg;
use crate::hw::Op;
use crate::names::encode;
use crate::tests_elab::{design, elab_only};

fn body(ss: &str) -> String {
    format!("module M() {{\n  input a: UInt[2];\n  input e: Bool;\n  input d: UInt[8];\n{ss}}}\n")
}

fn port(ss: &str) -> String {
    let b = Budget::default();
    elab_only(&body(ss), "M", b.fuel, b.depth)
}

fn port_at(ss: &str, fuel: u64) -> String {
    port_at_depth(ss, fuel, Budget::default().depth)
}

fn port_at_depth(ss: &str, fuel: u64, depth: u64) -> String {
    elab_only(&body(ss), "M", fuel, depth)
}

const M4: &str = "  mem m: [UInt[8]; 4];\n";
const WR: &str = "  write_port(m, a, d, e);\n";

fn rw() -> String {
    format!("{M4}{WR}  let r = m.read_port(a, e);\n")
}

/// A leaf of a binding: a leaf of a word with its offset and type, or a name.
fn leaves(ss: &str) -> Vec<(String, String)> {
    let d = design(&body(ss), "M");
    let Some(top) = d.insts.get(d.top) else {
        return Vec::new();
    };
    let name = |p| encode(&d.paths.name(p, &d.texts));
    top.body
        .lets
        .iter()
        .map(|l| {
            let node = d.graph.node(l.value);
            let text = match node.map(|n| (&n.op, &n.ty)) {
                Some((Op::Word(m, off), ty)) => {
                    format!("word {}@{off}:{}", name(*m), d.tys.text_of(ty))
                }
                Some((Op::Ref(p), _)) => format!("ref {}", name(*p)),
                _ => "other".to_owned(),
            };
            (name(l.path), text)
        })
        .collect()
}

type Request = (Option<Vec<String>>, Option<Vec<String>>);

/// The requests of each memory of the top instantiation, as the texts of their parts.
fn requests(ss: &str) -> Vec<Request> {
    let d = design(&body(ss), "M");
    let Some(top) = d.insts.get(d.top) else {
        return Vec::new();
    };
    let text = |a: &Agg| match a {
        Agg::Hw(h) => format!("hardware {}", d.tys.text_of(&d.graph.ty(*h))),
        Agg::Static(v) => v.text(&d.tys),
        _ => "other".to_owned(),
    };
    top.body
        .mems
        .iter()
        .map(|m| {
            (
                m.read.as_ref().map(|(x, y)| vec![text(x), text(y)]),
                m.write
                    .as_ref()
                    .map(|(x, y, z)| vec![text(x), text(y), text(z)]),
            )
        })
        .collect()
}

fn strings(xs: &[&str]) -> Vec<String> {
    xs.iter().map(|x| (*x).to_owned()).collect()
}

/// The memory records the first request of each kind after its typed uses. The response refers
/// to the word at the offset 0 and to `m$0rvalid`, and its binding binds each hardware leaf.
#[test]
fn the_memory_records_the_first_request_of_each_kind() {
    assert_eq!(port(&rw()), "ok 95");
    assert_eq!(
        requests(&rw()),
        [(
            Some(strings(&["hardware UInt[2]", "hardware Bool"])),
            Some(strings(&[
                "hardware UInt[2]",
                "hardware UInt[8]",
                "hardware Bool"
            ]))
        )]
    );
    let src = format!("{M4}  write_port(m, 1, 7, true);\n  let r = m.read_port(a, e);\n");
    assert_eq!(
        requests(&src),
        [(
            Some(strings(&["hardware UInt[2]", "hardware Bool"])),
            Some(strings(&["UInt[2]", "UInt[8]", "Bool"]))
        )]
    );
}

#[test]
fn the_response_leaves_refer_to_the_word_with_their_offsets() {
    let name = |x: &str, y: &str| (x.to_owned(), y.to_owned());
    assert_eq!(
        leaves(&rw()),
        [
            name("r$data", "word m@0:UInt[8]"),
            name("r$valid", "ref m$0rvalid")
        ]
    );
    let src = "  mem m: [(UInt[3], Bool, UInt[5]); 4];\n  write_port(m, a, (1, true, 2), e);\n  let r = m.read_port(a, e);\n";
    assert_eq!(
        leaves(src),
        [
            name("r$data$0e", "word m@0:UInt[3]"),
            name("r$data$1e", "word m@3:Bool"),
            name("r$data$2e", "word m@4:UInt[5]"),
            name("r$valid", "ref m$0rvalid"),
        ]
    );
}

/// The first argument is a memory, else `S010` at the call. The address has the type `UInt[A]`
/// with `A = max(1, ceil(log2 N))`, the enable `Bool`, and the data the word type: `S010` for
/// another hardware type, and `S012` for a static value that does not fit. The typed uses run
/// in the order of the arguments. A static address that fits but is not below `N` is valid.
#[test]
fn the_arguments_of_a_port_call_take_their_types() {
    let at = |tail: &str| port(&format!("{M4}{WR}{tail}"));
    assert_eq!(at("  let q = read_port(e, a, e);\n"), "S010 7:11");
    assert_eq!(at("  let q = read_port(5, a, e);\n"), "S010 7:11");
    assert_eq!(
        port(
            "  reg g: UInt[8] = 0;\n  g := g;\n  mem m: [UInt[8]; 4];\n  write_port(g, a, d, e);\n"
        ),
        "S010 8:3"
    );
    assert_eq!(
        port("  mem m: [UInt[8]; 3];\n  let r = read_port(m, d, e);\n"),
        "S010 6:11"
    );
    assert_eq!(
        port(&format!("{M4}  let r = read_port(m, a, d);\n")),
        "S010 6:11"
    );
    assert_eq!(
        port(&format!("{M4}  write_port(m, a, a, e);\n")),
        "S010 6:3"
    );
    assert_eq!(
        port(&format!("{M4}  let q = read_port(m, 4, d);\n")),
        "S012 6:11"
    );
    assert_eq!(
        port(&format!("{M4}  write_port(m, 4, 256, d);\n")),
        "S012 6:3"
    );
    assert_eq!(
        port(&format!("{M4}  write_port(m, a, 256, d);\n")),
        "S012 6:3"
    );
    assert_eq!(
        port("  mem m: [UInt[8]; 1];\n  write_port(m, 2, 1, true);\n"),
        "S012 6:3"
    );
    assert_eq!(
        port(
            "  mem m: [UInt[8]; 3];\n  write_port(m, 3, 1, true);\n  let r = read_port(m, 3, false);\n"
        ),
        "ok 106"
    );
    assert_eq!(
        port(
            "  mem m: [UInt[8]; 1];\n  write_port(m, 1, 1, true);\n  let r = read_port(m, 0, false);\n"
        ),
        "ok 106"
    );
}

/// A call in a hardware arm is `S016` at the call, after the memory check and before the typed
/// uses.
#[test]
fn a_port_call_in_a_hardware_arm_is_s016() {
    assert_eq!(
        port(&format!(
            "{M4}  let q = if (e) {{ read_port(m, 4, d) }} else {{ 1 }};\n"
        )),
        "S016 6:20"
    );
    assert_eq!(
        port(&format!(
            "{M4}  let q = if (e) {{ read_port(a, 4, d) }} else {{ 1 }};\n"
        )),
        "S010 6:20"
    );
}

/// `S018`: a second call of one kind is `S018` at the call, also by a receiver and through a
/// `let` alias. It waits for the end of the body, so a later error comes first. A memory without
/// a read or without a write is `S018` at its statement, and all of them compete by position.
#[test]
fn a_second_call_of_one_kind_is_s018_at_the_call() {
    let rr = format!("{}  let q = m.read_port(a, e);\n", rw());
    assert_eq!(port(&rr), "S018 8:11");
    assert_eq!(
        port(&format!("{}  m.write_port(a, d, e);\n", rw())),
        "S018 8:3"
    );
    assert_eq!(
        port(&format!(
            "{M4}  let k = m;\n  write_port(k, a, d, e);\n  let r = m.read_port(a, e);\n  let q = k.read_port(a, e);\n"
        )),
        "S018 9:11"
    );
    assert_eq!(port(&format!("{rr}  let z: Bool = d;\n")), "S010 9:3");
    assert_eq!(
        port(&format!("{M4}  let r = m.read_port(a, e);\n")),
        "S018 5:3"
    );
    assert_eq!(port(&format!("{M4}{WR}")), "S018 5:3");
    assert_eq!(
        port(&format!(
            "{M4}  mem n: [UInt[8]; 4];\n  write_port(n, a, d, e);\n  let r = read_port(n, a, e);\n  let q = read_port(n, a, e);\n"
        )),
        "S018 5:3"
    );
    assert_eq!(
        port(&format!(
            "{M4}{WR}{WR}  let r = read_port(m, a, e);\n  let q = read_port(m, a, e);\n"
        )),
        "S018 7:3"
    );
}

/// An error in the work of the prelude struct reports at the call (D7): the depth of
/// `ReadResponse[T]`.
#[test]
fn an_error_in_the_prelude_struct_reports_at_the_call() {
    assert_eq!(port_at_depth(&rw(), 100_000, 2), "S015 7:11");
    assert_eq!(port_at_depth(&rw(), 100_000, 3), "ok 95");
}

/// The zero size of the response is the last charge of the call. A second read charges as a
/// read with a done specialization of `ReadResponse[T]`, also of another memory. A wide word
/// charges the copy of its data and the zero size of its response, with no walk.
#[test]
fn the_charges_of_the_port_calls() {
    assert_eq!(port_at(&rw(), 95), "ok 95");
    assert_eq!(port_at(&rw(), 94), "S015 7:11");
    let rr = format!("{}  let q = m.read_port(a, e);\n", rw());
    assert_eq!(port_at(&rr, 110), "S018 8:11");
    assert_eq!(port_at(&rr, 109), "S015 8:11");
    let rww = format!("{}{WR}", rw());
    assert_eq!(port_at(&rww, 106), "S018 8:3");
    assert_eq!(port_at(&rww, 105), "S015 8:3");
    let spec8 = "  let t = ReadResponse[UInt[8]];\n";
    assert_eq!(port_at(&format!("{M4}{WR}"), 63), "S018 5:3");
    assert_eq!(port_at(&format!("{M4}{WR}"), 62), "S015 6:3");
    assert_eq!(port(&format!("{spec8}{}", rw())), "ok 107");
    assert_eq!(port_at(&format!("{spec8}{M4}{WR}"), 92), "S018 6:3");
    assert_eq!(port_at(&format!("{spec8}{M4}{WR}"), 91), "S015 7:3");
    let mn = format!(
        "{}  mem n: [UInt[8]; 4];\n  write_port(n, a, d, e);\n",
        rw()
    );
    assert_eq!(
        port(&format!("{mn}  let q = n.read_port(a, e);\n")),
        "ok 130"
    );
    assert_eq!(port_at(&mn, 115), "S018 8:3");
    assert_eq!(port_at(&mn, 114), "S015 9:3");
    let wide = |k: usize| {
        format!(
            "  input x: [Bool; {k}];\n  mem m: [[Bool; {k}]; 4];\n  let r = m.read_port(a, e);\n  write_port(m, a, x, e);\n"
        )
    };
    assert_eq!(port(&wide(4)), "ok 120");
    assert_eq!(port(&wide(4096)), format!("ok {}", 120 + 2 * (4096 - 4)));
}
