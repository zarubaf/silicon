// SPDX-License-Identifier: Apache-2.0
//! The words that a run makes (`Count::Words`). The charge sites do not see the work of a wide
//! constant or of a wide node, so the places that make them count their 64-bit words. The work
//! of a module grows linearly in the width of its values: doubling the width doubles the
//! growth. The tests count words and not time.

use crate::counters::of;
use crate::tests_flatten::lowered;

/// The words of the run of the module `M` with the body `body` at the width `w`. The width and
/// the family make the fuel budget of the run unique, and so the key of its counters.
fn words(family: u64, body: &str, w: u64) -> u64 {
    let fuel = 980_000_000 + family * 1_000_000 + w;
    let src =
        format!("enum P: UInt[1] {{ A(UInt[{w}], UInt[{w}]) = 1 }}\nmodule M() {{\n{body}}}\n")
            .replace("{w}", &w.to_string());
    let lowered = lowered(&src, "M", fuel);
    assert!(lowered.is_ok(), "{:?} at {w}", lowered.err());
    of(fuel).words
}

/// Each doubling of the width doubles the growth of the words. A product with another size
/// would break it.
fn assert_linear(family: u64, body: &str) {
    let at = |w: u64| words(family, body, w);
    let (w1, w2, w4, w8) = (at(1024), at(2048), at(4096), at(8192));
    assert!(w2 > w1, "{w1} {w2}");
    assert_eq!(w4 - w2, 2 * (w2 - w1), "{w1} {w2} {w4}");
    assert_eq!(w8 - w4, 2 * (w4 - w2), "{w2} {w4} {w8}");
}

/// A wide constant has one word for each 64 bits of its width.
#[test]
fn the_words_of_a_wide_constant_grow_linearly_in_its_width() {
    assert_linear(1, "  output o: UInt[{w}];\n  o := UInt[{w}](3);\n");
}

/// A wide `concat`: the payload of an enum with two wide leaves is a pack of the doubled width.
#[test]
fn the_words_of_a_wide_concat_grow_linearly_in_its_width() {
    assert_linear(
        2,
        "  input x: UInt[{w}];\n  input y: UInt[{w}];\n  output o: Bool;\n  \
         let a = P::A(x, y);\n  o := true;\n",
    );
}
