//! The guard on the Verilog that LEC imports. `circt-verilog --ir-hw` drops
//! the initial value of a register, so LEC cannot see it. A register with an
//! initial value hides a missing reset in simulation. The guard rejects each
//! form of an initial value: an `initial` process and a variable declaration
//! with `=`.

use anyhow::{Result, bail};

/// The keywords that declare a variable. A `wire` with `=` is a continuous
/// assignment, not an initial value.
const VARIABLES: [&str; 4] = ["reg", "logic", "bit", "integer"];

/// Fails if `sv` gives a register an initial value.
pub fn reject_initial_values(sv: &str) -> Result<()> {
    let code: String = sv
        .lines()
        .map(|l| l.split_once("//").map_or(l, |(code, _)| code))
        .collect::<Vec<_>>()
        .join("\n");
    for statement in code.split(';') {
        let words: Vec<&str> = statement
            .split(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == '$'))
            .filter(|w| !w.is_empty())
            .collect();
        if words.contains(&"initial") {
            bail!(
                "the Verilog has an `initial` process: `{}`",
                statement.trim()
            );
        }
        // An `automatic` variable gets its value on each entry of its block,
        // so its `=` is no initial value of a register.
        let declares = words.iter().any(|w| VARIABLES.contains(w)) && !words.contains(&"automatic");
        if declares && has_assignment(statement) {
            bail!(
                "the Verilog gives a variable an initial value: `{}`",
                statement.trim()
            );
        }
    }
    Ok(())
}

/// Whether `text` has an `=` that is not part of `==`, `<=`, `>=`, `!=`, or
/// `===`.
fn has_assignment(text: &str) -> bool {
    let bytes = text.as_bytes();
    bytes.iter().enumerate().any(|(i, &b)| {
        b == b'='
            && !matches!(
                i.checked_sub(1).map(|j| bytes[j]),
                Some(b'=' | b'<' | b'>' | b'!')
            )
            && bytes.get(i + 1) != Some(&b'=')
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_output_of_firtool_passes() {
        let sv = "module top(\n  input clk,\n  output [7:0] q\n);\n  reg [7:0] r; // r = 0\n  \
                  wire [7:0] _GEN = r + 8'h1;\n  always_ff @(posedge clk) begin\n    \
                  automatic logic [7:0] t;\n    t = r;\n    r <= t == 8'h0 ? _GEN : t;\n  end\n  \
                  assign q = r;\nendmodule\n";
        reject_initial_values(sv).unwrap();
    }

    #[test]
    fn an_initial_value_fails() {
        for (sv, message) in [
            (
                "  reg [3:0] r = 4'h0;\n",
                "the Verilog gives a variable an initial value: `reg [3:0] r = 4'h0`",
            ),
            (
                "module m(output reg [3:0] q = 0);\n",
                "the Verilog gives a variable an initial value: `module m(output reg [3:0] q = 0)`",
            ),
            (
                "  logic a, b = 1;\n",
                "the Verilog gives a variable an initial value: `logic a, b = 1`",
            ),
            (
                "  initial r = 0;\n",
                "the Verilog has an `initial` process: `initial r = 0`",
            ),
        ] {
            let error = reject_initial_values(sv).unwrap_err().to_string();
            assert_eq!(error, message);
        }
    }
}
