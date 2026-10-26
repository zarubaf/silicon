// SPDX-License-Identifier: Apache-2.0
//! The parts of the evaluator that need no source: the address width of a memory port (section
//! 7.6), and the records of `diagnostic` with the pending records of an early key (#387).

use super::mem::addr_width;
use super::observe::Records;
use super::{Res, fail};
use crate::Code;
use parse::ast::Pos;

#[test]
fn the_address_width_is_the_ceiling_of_the_log_with_a_minimum_of_one() {
    for (depth, width) in [
        (1, 1),
        (2, 1),
        (3, 2),
        (4, 2),
        (5, 3),
        (8, 3),
        (9, 4),
        (1 << 20, 20),
        ((1 << 20) + 1, 21),
        (16_777_215, 24),
        (16_777_216, 24),
    ] {
        assert_eq!(addr_width(depth), width, "{depth}");
    }
}

/// A failed check that drops the records of an early key at `pos`.
fn dropped_at(pos: Pos) -> Records {
    let mut records = Records::default();
    records.push("kept".to_owned());
    records.open();
    let mark = records.mark();
    records.push("early".to_owned());
    let failed: Res<()> = fail(Code::S013, pos, "out of range".to_owned());
    records.close(failed.as_ref().err().map(|e| (mark, e)));
    records
}

/// The walk keeps the records of an inner walk and of the early keys whose steps passed, and it
/// drops those after the failed check. The run ends with that check, so the assertion holds.
#[test]
fn a_failed_check_drops_only_the_pending_records_after_it() {
    let pos = Pos { line: 3, col: 7 };
    let mut records = Records::default();
    records.open();
    records.push("one".to_owned());
    records.open();
    records.push("inner".to_owned());
    records.close(None);
    let mark = records.mark();
    records.push("spin".to_owned());
    let failed: Res<()> = fail(Code::S013, pos, "out of range".to_owned());
    records.close(failed.as_ref().err().map(|e| (mark, e)));
    assert_eq!(records.finish(&failed), ["one", "inner"]);
    let failed: Res<()> = fail(Code::S013, pos, "out of range".to_owned());
    assert_eq!(dropped_at(pos).finish(&failed), ["kept"]);
}

/// A run that goes on after the failed check, as after an error that a later rule recovers
/// from, would show the early key. The assertion at the end of the run fires.
#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "a failed check after an early key did not end the run")]
fn a_run_that_goes_on_after_a_dropped_record_fails_the_assertion() {
    dropped_at(Pos { line: 3, col: 7 }).finish(&Ok(()));
}

/// A run that ends with another error than the check also fires the assertion.
#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "a failed check after an early key did not end the run")]
fn a_run_that_ends_with_another_error_fails_the_assertion() {
    let other: Res<()> = fail(Code::S015, Pos { line: 4, col: 1 }, "fuel".to_owned());
    dropped_at(Pos { line: 3, col: 7 }).finish(&other);
}
