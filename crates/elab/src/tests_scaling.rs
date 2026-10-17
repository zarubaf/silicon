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
//!
//! A template is a file of `tests/source/scaling/`. Its header has a line
//! `// SCALE <name> <n0> <n1> <n2> <n3> <n4>` and a line `// TOP <top>`. The placeholder `{N}`
//! stands for the size of the run. A block between `// REPEAT <i> <count>` and `// END` repeats
//! `count` times, and `{i}` stands for the number of the copy. Each budget fix adds a template
//! that makes the extreme shape of the fix and grows it.

use crate::counters::of;
use crate::tests_flatten::lowered;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

/// The constant of the absolute check: the next power of 2 of 4 times the largest `W / B` of
/// the templates.
const C: f64 = 0.5;

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

/// The absolute check on a series of points, one for each size. `Err` names the failed size.
#[allow(clippy::cast_precision_loss)]
fn within_bound(points: &[Point], c: f64) -> Result<(), String> {
    for (k, p) in points.iter().enumerate() {
        if p.w as f64 > c * p.bound() {
            return Err(format!(
                "k={k}: the work {} is above {c} * B = {:.0}",
                p.w,
                c * p.bound()
            ));
        }
    }
    Ok(())
}

/// The verdict on a series of runs with the whole fuel: the absolute check, then the growth.
#[allow(clippy::cast_precision_loss)]
fn judge(points: &[Point], c: f64) -> Result<(), String> {
    within_bound(points, c)?;
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
    if let Some(pair) = growths
        .windows(2)
        .find(|pair| pair.iter().all(|g| *g >= GROWTH))
    {
        return Err(format!(
            "the work for each unit of fuel grows at the exponents {pair:?}"
        ));
    }
    Ok(())
}

/// The number of the next run. It keeps the fuel of each run unique, so the counters of two
/// runs do not meet.
static RUNS: AtomicU64 = AtomicU64::new(0);

/// A run of the program text `src` with the top `top`. The error is the code and the position
/// of a rejection.
fn measure(src: &str, top: &str) -> Result<Point, String> {
    let fuel = (1u64 << 40) + RUNS.fetch_add(1, Ordering::Relaxed);
    let (_, run) = lowered(src, top, fuel)?;
    let counts = of(fuel);
    Ok(Point {
        w: counts.total(),
        f: run.used(),
        s: src.len() as u64,
        scan: counts.ast,
    })
}

/// A template: its name, its five sizes, its top, and its lines.
struct Template {
    name: String,
    sizes: Vec<u64>,
    top: String,
    lines: Vec<String>,
}

fn parse(text: &str) -> Result<Template, String> {
    let mut scale = None;
    let mut top = None;
    for line in text.lines() {
        if let Some(rest) = line.strip_prefix("// SCALE ") {
            scale = Some(
                rest.split_whitespace()
                    .map(str::to_owned)
                    .collect::<Vec<_>>(),
            );
        }
        if let Some(rest) = line.strip_prefix("// TOP ") {
            top = Some(rest.trim().to_owned());
        }
    }
    let scale = scale.ok_or("no `// SCALE` line")?;
    let (name, sizes) = scale.split_first().ok_or("an empty `// SCALE` line")?;
    let sizes = sizes
        .iter()
        .map(|n| n.parse::<u64>().map_err(|e| format!("size {n}: {e}")))
        .collect::<Result<Vec<_>, _>>()?;
    if sizes.len() != 5 {
        return Err(format!("{} sizes, not 5", sizes.len()));
    }
    Ok(Template {
        name: name.clone(),
        sizes,
        top: top.ok_or("no `// TOP` line")?,
        lines: text.lines().map(str::to_owned).collect(),
    })
}

/// The source of the template at the size `n`.
fn expand(t: &Template, n: u64) -> Result<String, String> {
    let mut out = String::new();
    let mut lines = t.lines.iter();
    while let Some(line) = lines.next() {
        let Some(rest) = line.strip_prefix("// REPEAT ") else {
            out.push_str(&line.replace("{N}", &n.to_string()));
            out.push('\n');
            continue;
        };
        let (var, count) = rest.split_once(' ').ok_or("a bad `// REPEAT` line")?;
        let count = count.replace("{N}", &n.to_string());
        let count: u64 = count
            .trim()
            .parse()
            .map_err(|e| format!("count {count}: {e}"))?;
        let mut block = Vec::new();
        for l in lines.by_ref() {
            if l.starts_with("// END") {
                break;
            }
            block.push(l);
        }
        for i in 0..count {
            for l in &block {
                out.push_str(
                    &l.replace("{N}", &n.to_string())
                        .replace(&format!("{{{var}}}"), &i.to_string()),
                );
                out.push('\n');
            }
        }
    }
    Ok(out)
}

/// The files of `tests/source/scaling/`.
fn templates() -> Vec<(PathBuf, String)> {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../tests/source/scaling");
    let mut files: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("{}: {e}", dir.display()))
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "si"))
        .collect();
    files.sort();
    files
        .into_iter()
        .map(|p| {
            let text =
                std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{}: {e}", p.display()));
            (p, text)
        })
        .collect()
}

/// The table of a series, for a failure.
fn table(sizes: &[u64], points: &[Point]) -> String {
    use std::fmt::Write as _;
    let mut out = String::from("      N        W        F      s\n");
    for (n, p) in sizes.iter().zip(points) {
        let _ = writeln!(out, "{n:>7} {:>8} {:>8} {:>6}", p.w, p.f, p.s);
    }
    out
}

/// The fractions of the fuel of a successful run at which the run must fail with `S015`. The
/// bound of the work holds at every budget (front-end spec 5.4), so a charge that comes after its
/// work shows here.
const FRACTIONS: [u64; 3] = [2, 4, 16];

/// The point of a run with the fuel `fuel` that ends in `S015`: the work that the run made before
/// it stopped, and the fuel as the budget.
fn capped(src: &str, top: &str, fuel: u64) -> Result<Point, String> {
    match lowered(src, top, fuel) {
        Ok(_) => Err(format!("the run with the fuel {fuel} succeeds")),
        Err(e) if e.starts_with("S015") => Ok(Point {
            w: of(fuel).total(),
            f: fuel,
            s: src.len() as u64,
            scan: of(fuel).ast,
        }),
        Err(e) => Err(format!("the run with the fuel {fuel} gives {e}")),
    }
}

/// Each template stays within the bound with the whole fuel and with a fraction of it, and grows
/// no faster than its fuel with the whole fuel. A template that the front end rejects fails: a template is a
/// program that the front end accepts.
#[test]
fn the_templates_stay_in_the_bound() {
    let all = templates();
    assert!(!all.is_empty(), "no template");
    for (path, text) in all {
        let t = parse(&text).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        let mut full = Vec::new();
        let mut cut: Vec<Vec<Point>> = vec![Vec::new(); FRACTIONS.len()];
        for n in &t.sizes {
            let src = expand(&t, *n).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
            let p = measure(&src, &t.top)
                .unwrap_or_else(|e| panic!("{}: N={n} is rejected: {e}\n{src}", t.name));
            for (series, d) in cut.iter_mut().zip(FRACTIONS) {
                let q = capped(&src, &t.top, p.f / d)
                    .unwrap_or_else(|e| panic!("{}: N={n}, fuel/{d}: {e}", t.name));
                series.push(q);
            }
            full.push(p);
        }
        if let Err(why) = judge(&full, C) {
            panic!("scaling {}: {why}\n{}", t.name, table(&t.sizes, &full));
        }
        for (series, d) in cut.iter().zip(FRACTIONS) {
            // The run stops in a phase that depends on the size, so the work for each unit of
            // fuel is not a growth here. Only the bound is.
            if let Err(why) = within_bound(series, C) {
                panic!(
                    "scaling {} at fuel/{d}: {why}\n{}",
                    t.name,
                    table(&t.sizes, series)
                );
            }
        }
    }
}

#[test]
fn a_template_expands_its_placeholders_and_repeats() {
    let t =
        parse("// SCALE s 1 2 3 4 5\n// TOP M()\nx{N}\n// REPEAT i {N}\na{i}\n// END\n").unwrap();
    assert_eq!(t.sizes, [1, 2, 3, 4, 5]);
    assert!(expand(&t, 3).unwrap().ends_with("x3\na0\na1\na2\n"));
    assert!(parse("// TOP M()\n").is_err());
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

/// Two steps in a row of excess growth fail, also when the last step is flat.
#[test]
fn early_excess_growth_fails() {
    let (w, f) = ([100, 200, 600, 2200, 5400], [100, 200, 400, 800, 1600]);
    let points: Vec<Point> = w
        .iter()
        .zip(f)
        .map(|(w, f)| Point {
            w: *w,
            f,
            s: 50,
            scan: 0,
        })
        .collect();
    assert!(judge(&points, 1.0e9).is_err_and(|e| e.contains("exponents")));
}

/// The absolute check fails when the work is above `C * B`.
#[test]
fn a_table_above_the_bound_fails() {
    let mut points = linear(0, 5);
    points[2].w = 10_000_000;
    assert!(judge(&points, 8.0).is_err_and(|e| e.contains("above")));
}
