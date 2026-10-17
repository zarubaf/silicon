// SPDX-License-Identifier: Apache-2.0
//! The judge of the scaling templates (issue #292, front-end spec 11.4). A template runs at five
//! growing sizes with the test counters. The work `W` is the sum of all counters of the run and
//! its lowering. The fuel `F` is the fuel that the run used. Two checks hold. The work stays
//! within `C * B(F, s)`, with `B = (F + s) * max(1, log2(F + s))` and `s` the source length.
//! The work for each unit of fuel does not grow when a size doubles. The checks count work and
//! never time, so the result is exact and the same on each machine.
//!
//! The absolute check guards against a regression. It does not show that the bound holds,
//! because `C` absorbs the escapes that exist when it is set.

/// The growth exponent at which two steps in a row fail: the work for each unit of fuel then
/// grows by a factor of at least `2^0.5` when a size doubles.
const GROWTH: f64 = 0.5;

/// The measure of one run.
#[derive(Clone, Copy, Debug, PartialEq)]
struct Point {
    /// The work: the sum of all counters.
    w: u64,
    /// The fuel of the elaboration with the lowering.
    f: u64,
    /// The length of the source text in bytes.
    s: u64,
    /// The part of the work that the scan of the source made: the bound pays for it with `s`.
    scan: u64,
}

impl Point {
    /// The bound `B(F, s)` of the front-end spec, section 5.4.
    #[allow(clippy::cast_precision_loss)]
    fn bound(&self) -> f64 {
        let n = (self.f + self.s) as f64;
        n * n.log2().max(1.0)
    }
}

/// The verdict on a series of points, one for each size. `Err` names the failed check.
#[allow(clippy::cast_precision_loss)]
fn judge(points: &[Point], c: f64) -> Result<(), String> {
    for (k, p) in points.iter().enumerate() {
        if p.w as f64 > c * p.bound() {
            return Err(format!(
                "k={k}: the work {} is above {c} * B = {:.0}",
                p.w,
                c * p.bound()
            ));
        }
    }
    // The increments cancel the part of the program that does not scale. `last` is the
    // increment of the step before, and `growths` holds the growth of each step that has one.
    let mut last: Option<f64> = None;
    let mut growths: Vec<f64> = Vec::new();
    for (k, pair) in points.windows(2).enumerate() {
        let (a, b) = (pair[0], pair[1]);
        // The scan of a longer source is work that the bound pays for with `s`, not with the
        // fuel, so the increments leave it out.
        let (dw, df) = (
            (b.w - b.scan).saturating_sub(a.w - a.scan),
            b.f.saturating_sub(a.f),
        );
        if df == 0 {
            if dw > 0 {
                return Err(format!(
                    "k={}: the work grew by {dw} and the fuel did not grow",
                    k + 1
                ));
            }
            continue;
        }
        let d = dw as f64 / df as f64;
        if d <= 0.0 {
            continue;
        }
        if let Some(before) = last {
            growths.push((d / before).log2());
        }
        last = Some(d);
    }
    let tail = &growths[growths.len().saturating_sub(2)..];
    if tail.len() == 2 && tail.iter().all(|g| *g >= GROWTH) {
        return Err(format!(
            "the work for each unit of fuel grows at the exponents {tail:?}"
        ));
    }
    Ok(())
}

fn linear(a: u64, b: u64) -> Vec<Point> {
    (0..5)
        .map(|k| Point {
            w: a + b * (1 << k),
            f: 10 + 3 * (1 << k),
            s: 50,
            scan: 0,
        })
        .collect()
}

/// A table whose work is linear in the fuel passes.
#[test]
fn a_linear_table_passes() {
    assert_eq!(judge(&linear(0, 5), 8.0), Ok(()));
}

/// A table with a large fixed part and a linear growth passes: the increments cancel the part.
#[test]
fn a_table_with_a_large_fixed_part_passes() {
    assert_eq!(judge(&linear(40_000, 5), 1000.0), Ok(()));
}

/// A table whose work grows with the square of the fuel fails.
#[test]
fn a_quadratic_table_fails() {
    let points: Vec<Point> = (0..5)
        .map(|k| {
            let f = 100u64 << k;
            Point {
                w: f * f / 50,
                f,
                s: 50,
                scan: 0,
            }
        })
        .collect();
    assert!(judge(&points, 1.0e9).is_err());
}

/// A table whose work grows and whose fuel does not fails.
#[test]
fn work_with_no_fuel_fails() {
    let mut points = linear(0, 5);
    points[3].f = points[2].f;
    assert!(judge(&points, 1.0e9).is_err_and(|e| e.contains("did not grow")));
}

/// A step with no growth of work and of fuel does not count, and the growth compares the steps
/// around it.
#[test]
fn a_vacuous_step_is_skipped() {
    let mut points = linear(0, 5);
    points[3] = points[2];
    points[4] = Point {
        w: points[2].w + 2 * (points[2].w - points[1].w),
        f: points[2].f + 2 * (points[2].f - points[1].f),
        s: 50,
        scan: 0,
    };
    assert_eq!(judge(&points, 1.0e9), Ok(()));
}

/// The absolute check fails when the work is above `C * B`.
#[test]
fn a_table_above_the_bound_fails() {
    let mut points = linear(0, 5);
    points[2].w = 10_000_000;
    assert!(judge(&points, 8.0).is_err_and(|e| e.contains("above")));
}
