// SPDX-License-Identifier: Apache-2.0
//! Port families, keyed ports, and helpers that declare a port (front-end
//! spec 5.6).
//!
//! Every draw comes from the port tape (`on_port`), which no other form
//! reads, and choice 0 is no form. A program without port forms is thus the
//! program of the other tapes alone.
//!
//! The signature of a module holds a plan, so that a parent knows which
//! ports to bind and read before the body of the child exists. The body
//! carries the plan out at the start of its top frame. A plan fits every
//! context of its module: its keys and names are literals.
//!
//! Rules by construction, from the ledger of the table of public names
//! (spec 5.6):
//!
//! - A scalar name is fresh (`c<n>`, or one core keyword that is no keyword
//!   of Silicon), so no second scalar takes it (`S019`). A family is fresh
//!   too (`A<n>` for inputs, `Z<n>` for outputs, `K<n>` for the family of a
//!   helper), so no scalar takes it and no family has two directions. The
//!   ledger holds a family of an arm that does not run from the start.
//! - A key is a literal below 32, so it is a `Nat` in range (`S010`,
//!   `S012`), and a family gets each key once (`S019`). A `PortKey` that
//!   joins a family takes a key that the family lacks, on a port of the
//!   direction of the family.
//! - An entry or a keyed output gets one `:=`, in the block that declares it
//!   (`S018`). A child input gets one `:=` where its parent makes the
//!   instance.
//! - A port stands in the top frame of a module body, in a loop or an arm
//!   there, or in a helper that a `let` or a statement of that frame calls.
//!   It never stands in a hardware arm, under a guard of a helper, or in a
//!   `comptime fn` (`S016`, `S011`, `S006`).
//! - No local of a module takes a public name: the locals have other
//!   prefixes (`S019`, "Port name taken").
//! - The values of entries and keyed inputs go into the pool `port` of the
//!   scope, which only this tape reads. They reach the outputs through
//!   `mix_port` at the end of the body.

use super::hw::{Want, adapt};
use super::inst::Child;
use super::reflect::RTy;
use super::stat::{bin, int};
use super::{Builder, Built, Ctx, Hw, Lane, Module, Names};
use crate::eval::Fault;
use crate::program::{
    FTy, HBin, HExpr, Item, PTy, Place, Port, SBin, SExpr, STy, Scalar, Stmt, Ty,
};
use crate::public::Public;
use std::collections::{BTreeMap, BTreeSet};

/// The most families and keyed ports of one module.
const FAMILIES: usize = 3;
const KEYED: u32 = 4;
/// The most calls of port helpers in one module: each call counts, a helper
/// with a family is called two or three times.
const CALLS: u32 = 4;
/// The most helpers that declare a port.
const PORT_HELPERS: u32 = 2;
/// The most ports that the plans of one program declare.
pub(super) const MAX_PORTS: usize = 24;
/// The most entries that one top form declares. Joins and helper calls
/// add more entries to a family. Then the least key that no form uses.
const ENTRIES: u32 = 3;
const KEY_LIMIT: u32 = 32;
/// The depth of the values that the port forms draw: small, so that the
/// mean text of a program stays near its bound.
const PORT_DEPTH: u32 = 0;
/// The keys of the entries at the top: `2` and `10` sort differently as
/// numbers and as text.
const KEYS: [u32; 7] = [0, 1, 2, 3, 10, 11, 12];
/// The strides and offsets of the keys of a loop: `j * stride + offset`.
const STRIDES: [u32; 4] = [1, 4, 8, 8];
const OFFSETS: [u32; 3] = [0, 2, 2];
/// The names of core keywords that are no keyword of Silicon. A port with
/// one of them as its public name gets the core field `0k` (spec 7.2).
const CORE: [&str; 6] = ["add", "sub", "xor", "mux", "concat", "extract"];

/// The direction of a port.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Dir {
    In,
    Out,
}

/// A port that a plan declares when its module runs: what a parent binds
/// (an input) or reads (an output).
#[derive(Clone, Debug)]
pub(super) struct Declared {
    pub(super) dir: Dir,
    pub(super) public: Public,
    pub(super) ty: PTy,
}

/// How a family declares its entries.
#[derive(Clone, Debug)]
pub(super) enum Shape {
    /// One statement for each entry, at the top. Each entry has its own
    /// type, and an input of type `()` has no leaf.
    Top(Vec<(u32, PTy)>),
    /// `comptime for j in 0..count { input fam[j * stride + offset]: T; }`
    Loop {
        count: u32,
        stride: u32,
        offset: u32,
        ty: Ty,
    },
    /// `comptime if (true) { run } else { skipped }`, or the arms swapped.
    /// The arm that does not run declares entries of the family `skipped_fam`
    /// that never exist.
    Arm {
        run: Vec<(u32, Ty)>,
        skipped_fam: String,
        skipped: Vec<(u32, Ty)>,
        then_runs: bool,
    },
}

/// The `as` key of a keyed port.
#[derive(Clone, Debug)]
pub(super) enum Key {
    /// `as "name"`, also a core keyword.
    Str(String),
    /// `as PortKey("name", false, 0)`.
    Scalar(String),
    /// `as PortKey("fam", true, k)`: the entry `fam[k]`.
    Join(String, u32),
}

/// A form of the body of a module.
#[derive(Clone, Debug)]
pub(super) enum Form {
    Family {
        dir: Dir,
        fam: String,
        shape: Shape,
    },
    Keyed {
        dir: Dir,
        key: Key,
        ty: Ty,
    },
    /// `comptime for j in 0..count { input y: T as "c" + str(j + first); }`
    KeyedLoop {
        dir: Dir,
        first: u32,
        count: u32,
        ty: Ty,
    },
    /// `let l = HP(...);`, `calls` times: a helper that takes a name `c<first>`,
    /// or a key `0..calls`.
    Call {
        helper: usize,
        first: u32,
        calls: u32,
    },
}

/// What a module declares: its forms, in the order of its body.
#[derive(Clone, Debug, Default)]
pub(super) struct PortPlan {
    pub(super) forms: Vec<Form>,
}

/// What a helper that declares a port takes and declares.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum HelperKind {
    /// `fn HP(comptime x0: String) -> T { input y0: T as x0; return y0; }`
    Name,
    /// `fn HP(comptime x0: Nat) -> T { input fam[x0]: T; return ...; }`
    /// where the result adds the entry of the call before.
    Family(String),
}

/// A helper `HP<k>` that declares one port for each call.
#[derive(Clone, Debug)]
pub(super) struct PortHelper {
    pub(super) name: String,
    pub(super) kind: HelperKind,
    pub(super) ty: Ty,
}

impl PortPlan {
    /// The ports that the module declares when it runs, in the order of the
    /// forms.
    pub(super) fn declared(&self, helpers: &[PortHelper]) -> Vec<Declared> {
        let mut out = Vec::new();
        for form in &self.forms {
            form.declared(helpers, &mut out);
        }
        out
    }

    /// The families that only an arm that does not run declares: no
    /// declaration of the plan runs for them, so the table of public names
    /// holds them from the start and nothing else (spec 5.6).
    #[cfg(test)]
    pub(super) fn untaken_families(&self, helpers: &[PortHelper]) -> BTreeSet<String> {
        let running: BTreeSet<String> = self
            .declared(helpers)
            .into_iter()
            .map(|d| d.public.base)
            .collect();
        self.forms
            .iter()
            .filter_map(|f| match f {
                Form::Family {
                    shape:
                        Shape::Arm {
                            skipped_fam,
                            skipped,
                            ..
                        },
                    ..
                } if !skipped.is_empty() => Some(skipped_fam.clone()),
                _ => None,
            })
            .filter(|fam| !running.contains(fam))
            .collect()
    }
}

fn entry(fam: &str, key: u32) -> Public {
    Public {
        base: fam.to_owned(),
        key: Some(key),
    }
}

impl Form {
    fn declared(&self, helpers: &[PortHelper], out: &mut Vec<Declared>) {
        let mut push = |dir, public, ty| out.push(Declared { dir, public, ty });
        match self {
            Form::Family { dir, fam, shape } => match shape {
                Shape::Top(entries) => {
                    for (k, ty) in entries {
                        push(*dir, entry(fam, *k), ty.clone());
                    }
                }
                Shape::Loop {
                    count,
                    stride,
                    offset,
                    ty,
                } => {
                    for j in 0..*count {
                        push(*dir, entry(fam, j * stride + offset), PTy::Data(ty.clone()));
                    }
                }
                Shape::Arm { run, .. } => {
                    for (k, ty) in run {
                        push(*dir, entry(fam, *k), PTy::Data(ty.clone()));
                    }
                }
            },
            Form::Keyed { dir, key, ty } => {
                let public = match key {
                    Key::Str(n) | Key::Scalar(n) => Public::scalar(n),
                    Key::Join(fam, k) => entry(fam, *k),
                };
                push(*dir, public, PTy::Data(ty.clone()));
            }
            Form::KeyedLoop {
                dir,
                first,
                count,
                ty,
            } => {
                for j in 0..*count {
                    let name = format!("c{}", first + j);
                    push(*dir, Public::scalar(&name), PTy::Data(ty.clone()));
                }
            }
            Form::Call {
                helper,
                first,
                calls,
            } => {
                let Some(h) = helpers.get(*helper) else {
                    return;
                };
                match &h.kind {
                    HelperKind::Name => {
                        let name = format!("c{first}");
                        push(Dir::In, Public::scalar(&name), PTy::Data(h.ty.clone()));
                    }
                    HelperKind::Family(fam) => {
                        for k in 0..*calls {
                            push(Dir::In, entry(fam, k), PTy::Data(h.ty.clone()));
                        }
                    }
                }
            }
        }
    }
}

/// The table of public names while a plan is drawn: the families with
/// their direction and keys, and the next fresh name of each kind.
#[derive(Default)]
struct Ledger {
    families: BTreeMap<String, (Dir, BTreeSet<u32>)>,
    next_a: u32,
    next_z: u32,
    next_c: u32,
    core: bool,
    keyed: u32,
    calls: u32,
    /// The helpers whose family this module already uses.
    used: BTreeSet<usize>,
}

impl Ledger {
    /// A fresh family name for `dir`, in the table with no keys.
    fn family(&mut self, dir: Dir) -> String {
        let name = match dir {
            Dir::In => {
                self.next_a += 1;
                format!("A{}", self.next_a - 1)
            }
            Dir::Out => {
                self.next_z += 1;
                format!("Z{}", self.next_z - 1)
            }
        };
        self.families.insert(name.clone(), (dir, BTreeSet::new()));
        name
    }

    /// A fresh scalar name.
    fn name(&mut self) -> u32 {
        self.next_c += 1;
        self.next_c - 1
    }

    /// Takes the key `k` of the family `fam` if it is free.
    fn take(&mut self, fam: &str, k: u32) -> bool {
        self.families
            .get_mut(fam)
            .is_some_and(|(_, keys)| k < KEY_LIMIT && keys.insert(k))
    }
}

/// The key `j * stride + offset` of a loop over `binder`.
fn loop_key(binder: &str, stride: u32, offset: u32) -> SExpr {
    let at = bin(SBin::Mul, SExpr::Name(binder.to_owned()), lit(stride));
    bin(SBin::Add, at, lit(offset))
}

fn lit(n: u32) -> SExpr {
    int(i64::from(n))
}

fn string(s: &str) -> SExpr {
    SExpr::Str(s.to_owned())
}

/// `"c" + str(j + first)`, the public name of iteration `j`.
fn computed_name(binder: &str, first: u32) -> SExpr {
    let at = if first == 0 {
        SExpr::Name(binder.to_owned())
    } else {
        bin(SBin::Add, SExpr::Name(binder.to_owned()), lit(first))
    };
    bin(SBin::Add, string("c"), SExpr::StrOf(Box::new(at)))
}

/// The operator that folds an entry into an accumulator of its type.
fn fold(ty: &Ty) -> HBin {
    if matches!(ty, Ty::Bool) {
        HBin::Ne
    } else {
        HBin::Xor
    }
}

fn port(output: bool, name: &str, key: Option<SExpr>, public: Option<SExpr>, ty: PTy) -> Stmt {
    Stmt::Port(Port {
        output,
        name: name.to_owned(),
        key,
        public,
        ty,
    })
}

/// The type of the entry of a family that `@TypeOf` reflects: its data type,
/// or `Unit` for an empty entry.
fn entry_ty(ty: &PTy) -> Option<RTy> {
    match ty {
        PTy::Data(t) => RTy::of(t),
        PTy::Unit => Some(RTy::Unit),
    }
}

impl Builder {
    /// Runs `f` with the port tape as the tape, isolated from the other
    /// tapes (see `isolated`).
    pub(super) fn on_port<T>(&mut self, f: impl FnOnce(&mut Builder) -> T) -> T {
        self.isolated(Lane::Port, f)
    }

    /// The items of the helpers that declare a port.
    pub(super) fn port_helper_items(&self) -> Vec<Item> {
        self.port_helpers
            .iter()
            .enumerate()
            .filter(|(i, _)| self.port_helper_used.contains(i))
            .map(|(_, h)| {
                let formal = |t| vec![("x0".to_owned(), FTy::Static(t))];
                let name = |n: &str| HExpr::Name(n.to_owned());
                match &h.kind {
                    HelperKind::Name => Item::Helper {
                        name: h.name.clone(),
                        params: formal(STy::Str),
                        mut_first: false,
                        ret: FTy::Data(h.ty.clone()),
                        body: vec![port(
                            false,
                            "y0",
                            None,
                            Some(SExpr::Name("x0".to_owned())),
                            PTy::Data(h.ty.clone()),
                        )],
                        result: name("y0"),
                    },
                    HelperKind::Family(fam) => {
                        let entry = |k: SExpr| HExpr::Entry(fam.clone(), k);
                        let x0 = SExpr::Name("x0".to_owned());
                        let before = bin(SBin::Sub, x0.clone(), int(1));
                        let first = bin(SBin::Eq, x0.clone(), int(0));
                        let sum = HExpr::Binary(
                            HBin::Addw,
                            Box::new(entry(x0.clone())),
                            Box::new(entry(before)),
                        );
                        Item::Helper {
                            name: h.name.clone(),
                            params: formal(STy::Nat),
                            mut_first: false,
                            ret: FTy::Data(h.ty.clone()),
                            body: vec![port(false, fam, Some(x0), None, PTy::Data(h.ty.clone()))],
                            result: HExpr::If(
                                Box::new(HExpr::Static(first)),
                                Box::new(entry(int(0))),
                                Box::new(sum),
                            ),
                        }
                    }
                }
            })
            .collect()
    }

    /// The plan of a module. Choice 0 of the first draw is no plan. The top
    /// has one more often than a child, because its ports are the vectors
    /// and a child costs the binding and the reading in its parent.
    pub(super) fn port_plan(&mut self, top: bool) -> PortPlan {
        self.on_port(|b| {
            let mut plan = PortPlan::default();
            if b.tape.below(if top { 3 } else { 2 }) == 0 {
                return plan;
            }
            let mut ledger = Ledger::default();
            for _ in 0..b.tape.between(1, 2) {
                let mut forms = Vec::new();
                b.port_form(&mut ledger, &mut forms);
                for form in forms {
                    let mut declared = Vec::new();
                    form.declared(&b.port_helpers, &mut declared);
                    if b.port_count + declared.len() > MAX_PORTS {
                        continue;
                    }
                    b.port_count += declared.len();
                    plan.forms.push(form);
                }
            }
            plan
        })
    }

    /// The type of a port: `Bool`, or a literal width of at most 8 bits, so
    /// that a port adds little text.
    fn port_ty(&mut self) -> Ty {
        let w = self.tape.between(1, 8);
        match self.tape.below(4) {
            0 => Ty::Bool,
            1 | 2 => Ty::UInt(lit(w)),
            _ => Ty::SInt(lit(w)),
        }
    }

    fn dir(&mut self) -> Dir {
        if self.tape.flag() { Dir::In } else { Dir::Out }
    }

    /// A key from `KEYS` that `fam` does not have, taken in the ledger.
    fn fresh_key(&mut self, ledger: &mut Ledger, fam: &str) -> Option<u32> {
        (0..KEYS.len())
            .map(|_| self.pick(&KEYS))
            .find(|&k| ledger.take(fam, k))
    }

    /// The forms of one draw, or none when a cap or the ledger leaves no
    /// draw. A join and a call may add the family or the helper that they
    /// need.
    fn port_form(&mut self, led: &mut Ledger, forms: &mut Vec<Form>) {
        match self.tape.below(16) {
            0 | 1 => self.loop_form(led, forms),
            2 | 3 => self.top_form(led, forms),
            4 | 5 => self.arm_form(led, forms),
            6 => self.keyed_form(led, forms, false),
            7 | 8 => self.keyed_form(led, forms, true),
            9 | 10 => self.join_form(led, forms),
            11 => self.keyed_loop_form(led, forms),
            12 | 13 => self.call_form(led, forms, false),
            _ => self.call_form(led, forms, true),
        }
    }

    /// A family with a loop over its keys.
    fn loop_form(&mut self, led: &mut Ledger, forms: &mut Vec<Form>) {
        if led.families.len() >= FAMILIES {
            return;
        }
        let dir = self.dir();
        let fam = led.family(dir);
        let (count, stride, offset) = (
            self.tape.between(2, 3),
            self.pick(&STRIDES),
            self.pick(&OFFSETS),
        );
        (0..count).for_each(|j| {
            led.take(&fam, j * stride + offset);
        });
        let ty = self.port_ty();
        let shape = Shape::Loop {
            count,
            stride,
            offset,
            ty,
        };
        forms.push(Form::Family { dir, fam, shape });
    }

    /// A family with entries at the top, one of them sometimes empty.
    fn top_form(&mut self, led: &mut Ledger, forms: &mut Vec<Form>) {
        if led.families.len() >= FAMILIES {
            return;
        }
        let dir = self.dir();
        let fam = led.family(dir);
        let mut entries = Vec::new();
        for _ in 0..self.tape.between(1, ENTRIES) {
            let Some(k) = self.fresh_key(led, &fam) else {
                continue;
            };
            let ty = if self.tape.below(3) == 0 {
                PTy::Unit
            } else {
                PTy::Data(self.port_ty())
            };
            entries.push((k, ty));
        }
        let shape = Shape::Top(entries);
        forms.push(Form::Family { dir, fam, shape });
    }

    /// A family with entries in the arms of a `comptime if`.
    fn arm_form(&mut self, led: &mut Ledger, forms: &mut Vec<Form>) {
        if led.families.len() + 1 >= FAMILIES {
            return;
        }
        let dir = self.dir();
        let fam = led.family(dir);
        let mut run = Vec::new();
        for _ in 0..self.tape.between(1, 2) {
            if let Some(k) = self.fresh_key(led, &fam) {
                run.push((k, self.port_ty()));
            }
        }
        // The arm that does not run declares entries too: of the same
        // family, or of another one. The table holds both families from the
        // start.
        let skipped_fam = if self.tape.flag() {
            fam.clone()
        } else {
            led.family(dir)
        };
        let mut skipped = Vec::new();
        if let Some(k) = self.fresh_key(led, &skipped_fam) {
            skipped.push((k, self.port_ty()));
        }
        let then_runs = self.tape.flag();
        let shape = Shape::Arm {
            run,
            skipped_fam,
            skipped,
            then_runs,
        };
        forms.push(Form::Family { dir, fam, shape });
    }

    /// A keyed port with a `String` key or a scalar `PortKey`. The key is a
    /// core keyword once in a module.
    fn keyed_form(&mut self, led: &mut Ledger, forms: &mut Vec<Form>, portkey: bool) {
        if led.keyed >= KEYED {
            return;
        }
        led.keyed += 1;
        let dir = self.dir();
        let ty = self.port_ty();
        let key = if !led.core && self.tape.flag() {
            led.core = true;
            Key::Str(CORE[self.tape.index(CORE.len())].to_owned())
        } else if portkey {
            Key::Scalar(format!("c{}", led.name()))
        } else {
            Key::Str(format!("c{}", led.name()))
        };
        forms.push(Form::Keyed { dir, key, ty });
    }

    /// A keyed port `as PortKey(fam, true, k)` in a family, on a port of the
    /// direction of the family. A module without a family gets one first.
    fn join_form(&mut self, led: &mut Ledger, forms: &mut Vec<Form>) {
        if led.keyed >= KEYED {
            return;
        }
        if led.families.is_empty() {
            self.top_form(led, forms);
        }
        let names: Vec<String> = led.families.keys().cloned().collect();
        let Some(fam) = names.get(self.tape.index(names.len())).cloned() else {
            return;
        };
        let Some((dir, _)) = led.families.get(&fam).cloned() else {
            return;
        };
        let Some(k) = (0..KEY_LIMIT)
            .map(|_| self.tape.below(KEY_LIMIT))
            .find(|&k| led.take(&fam, k))
        else {
            return;
        };
        led.keyed += 1;
        let ty = self.port_ty();
        let key = Key::Join(fam, k);
        forms.push(Form::Keyed { dir, key, ty });
    }

    /// A loop of keyed ports with computed names.
    fn keyed_loop_form(&mut self, led: &mut Ledger, forms: &mut Vec<Form>) {
        let count = self.tape.between(2, 3);
        if led.keyed + count > KEYED {
            return;
        }
        led.keyed += count;
        let dir = self.dir();
        let first = led.next_c;
        led.next_c += count;
        let ty = self.port_ty();
        forms.push(Form::KeyedLoop {
            dir,
            first,
            count,
            ty,
        });
    }

    /// A call of a helper that declares a port, of the kind that `family`
    /// asks. The program makes the helper at its first call, and it has at
    /// most `PORT_HELPERS` of them. A helper with a family is called with
    /// the keys `0..calls`, in this order, and once in a module, because its
    /// family is the family of the module.
    fn call_form(&mut self, led: &mut Ledger, forms: &mut Vec<Form>, family: bool) {
        // A helper with a family needs at least two calls.
        if led.calls + if family { 2 } else { 1 } > CALLS {
            return;
        }
        let is_kind = |h: &PortHelper| matches!(h.kind, HelperKind::Family(_)) == family;
        let fit: Vec<usize> = (0..self.port_helpers.len())
            .filter(|&i| self.port_helpers.get(i).is_some_and(is_kind) && !led.used.contains(&i))
            .collect();
        let helper = match fit.get(self.tape.index(fit.len())) {
            Some(&i) if self.port_helpers.len() >= PORT_HELPERS as usize || self.tape.flag() => i,
            _ if self.port_helpers.len() < PORT_HELPERS as usize => self.make_helper(family),
            Some(&i) => i,
            None => return,
        };
        led.used.insert(helper);
        if family {
            let calls = self.tape.between(2, 3.min(CALLS - led.calls));
            led.calls += calls;
            forms.push(Form::Call {
                helper,
                first: 0,
                calls,
            });
        } else {
            let first = led.name();
            led.calls += 1;
            forms.push(Form::Call {
                helper,
                first,
                calls: 1,
            });
        }
    }

    /// A new helper `HP<k>`: one that takes a `comptime` name, or one that
    /// takes a `comptime` key.
    fn make_helper(&mut self, family: bool) -> usize {
        let k = self.port_helpers.len();
        let name = format!("HP{k}");
        let helper = if family {
            // The result adds two entries, so the type is finite.
            let w = self.tape.between(1, 8);
            PortHelper {
                name,
                kind: HelperKind::Family(format!("K{k}")),
                ty: Ty::UInt(lit(w)),
            }
        } else {
            let ty = self.port_ty();
            PortHelper {
                name,
                kind: HelperKind::Name,
                ty,
            }
        };
        self.port_helpers.push(helper);
        k
    }

    /// The value of an output entry or a keyed output: a hardware
    /// expression over the names of the scope, or `()`.
    fn port_value(&mut self, ctx: &Ctx, ty: &PTy) -> Built<HExpr> {
        let PTy::Data(t) = ty else {
            return Ok(HExpr::Unit);
        };
        let types = self.types(t, &ctx.envs)?;
        let want = Want {
            types,
            ty: Some(t.clone()),
        };
        Ok(self.driver_at(&ctx.port_view(), &want, PORT_DEPTH))
    }

    /// Makes `expr` of type `ty` a readable name of the port pool.
    fn pool(&mut self, ctx: &mut Ctx, expr: HExpr, ty: &Ty) -> Built {
        let types = self.types(ty, &ctx.envs)?;
        // `@TypeOf(req[k])` of a family entry gives its data type.
        if matches!(expr, HExpr::Entry(..)) {
            self.add_root(&crate::program::hexpr(&expr), RTy::of(ty));
        }
        ctx.port.push(Hw {
            expr,
            ty: Some(ty.clone()),
            types,
            mutable: false,
        });
        Ok(())
    }

    /// `let mut g: T = 0;`, the accumulator of the entries of a form. The
    /// name joins the pool after the form folded its entries in.
    fn accumulator(names: &mut Names, ty: &Ty, out: &mut Vec<Stmt>) -> String {
        let name = names.fresh("X");
        let init = HExpr::Static(match ty {
            Ty::Bool => SExpr::Bool(false),
            _ => int(0),
        });
        out.push(Stmt::Let {
            name: name.clone(),
            mutable: true,
            ty: Some(ty.clone()),
            value: init,
        });
        name
    }

    /// `g = g ^ e;` (`!=` for a `Bool`).
    fn fold_in(g: &str, ty: &Ty, e: HExpr) -> Stmt {
        let acc = HExpr::Name(g.to_owned());
        Stmt::Assign(
            g.to_owned(),
            HExpr::Binary(fold(ty), Box::new(acc), Box::new(e)),
        )
    }

    /// Carries out the plan of the module at the start of its top frame.
    pub(super) fn port_forms(
        &mut self,
        ctx: &mut Ctx,
        m: &mut Module,
        plan: &PortPlan,
        out: &mut Vec<Stmt>,
    ) -> Built {
        self.on_port(|b| {
            #[cfg(test)]
            {
                b.stats.skipped_families +=
                    u32::try_from(plan.untaken_families(&b.port_helpers).len()).unwrap_or(u32::MAX);
            }
            for form in &plan.forms {
                match form {
                    Form::Family { dir, fam, shape } => {
                        b.family(ctx, m, (*dir, fam), shape, out)?;
                    }
                    Form::Keyed { dir, key, ty } => b.keyed(ctx, m, *dir, key, ty, out)?,
                    Form::KeyedLoop {
                        dir,
                        first,
                        count,
                        ty,
                    } => b.keyed_loop(ctx, m, *dir, (*first, *count), ty, out)?,
                    Form::Call {
                        helper,
                        first,
                        calls,
                    } => b.helper_calls(ctx, m, (*helper, *first, *calls), out)?,
                }
            }
            Ok(())
        })
    }

    /// The entries of one family.
    fn family(
        &mut self,
        ctx: &mut Ctx,
        m: &mut Module,
        (dir, fam): (Dir, &str),
        shape: &Shape,
        out: &mut Vec<Stmt>,
    ) -> Built {
        let output = dir == Dir::Out;
        match shape {
            Shape::Top(entries) => {
                for (k, ty) in entries {
                    out.push(port(output, fam, Some(lit(*k)), None, ty.clone()));
                    note!(self, fam_tops);
                    note!(self, empty_entries, matches!(ty, PTy::Unit));
                    self.bind_or_read(ctx, (dir, fam, lit(*k)), ty, out)?;
                }
            }
            Shape::Loop {
                count,
                stride,
                offset,
                ty,
            } => {
                let binder = m.names.fresh("j");
                let key = loop_key(&binder, *stride, *offset);
                let mut body = vec![port(
                    output,
                    fam,
                    Some(key.clone()),
                    None,
                    PTy::Data(ty.clone()),
                )];
                if output {
                    let value = self.port_value(ctx, &PTy::Data(ty.clone()))?;
                    body.push(Stmt::Connect(Place::Entry(fam.to_owned(), key), value));
                    note!(self, own_targets);
                }
                out.push(Stmt::For(binder, lit(0), lit(*count), body));
                note!(self, fam_loops);
                if !output {
                    // A second loop reads the keys of the first.
                    let g = Self::accumulator(&mut m.names, ty, out);
                    let reader = m.names.fresh("j");
                    let key = loop_key(&reader, *stride, *offset);
                    let read = HExpr::Entry(fam.to_owned(), key);
                    let body = vec![Self::fold_in(&g, ty, read)];
                    out.push(Stmt::For(reader, lit(0), lit(*count), body));
                    note!(self, second_loops);
                    note!(self, own_selects);
                    self.pool(ctx, HExpr::Name(g), ty)?;
                }
            }
            Shape::Arm {
                run,
                skipped_fam,
                skipped,
                then_runs,
            } => {
                let mut taken = Vec::new();
                for (k, ty) in run {
                    let pty = PTy::Data(ty.clone());
                    taken.push(port(output, fam, Some(lit(*k)), None, pty.clone()));
                    if output {
                        let value = self.port_value(ctx, &pty)?;
                        taken.push(Stmt::Connect(Place::Entry(fam.to_owned(), lit(*k)), value));
                        note!(self, own_targets);
                    }
                }
                let idle: Vec<Stmt> = skipped
                    .iter()
                    .map(|(k, ty)| {
                        port(
                            output,
                            skipped_fam,
                            Some(lit(*k)),
                            None,
                            PTy::Data(ty.clone()),
                        )
                    })
                    .collect();
                let (then, els) = if *then_runs {
                    (taken, idle)
                } else {
                    (idle, taken)
                };
                out.push(Stmt::If(SExpr::Bool(*then_runs), then, Some(els)));
                note!(self, fam_arms);
                if !output {
                    for (k, ty) in run {
                        let read = HExpr::Entry(fam.to_owned(), lit(*k));
                        self.pool(ctx, read, ty)?;
                        note!(self, own_selects);
                    }
                }
            }
        }
        Ok(())
    }

    /// An entry at the top: an output gets its `:=`, and an input of data
    /// becomes a readable name of the pool.
    fn bind_or_read(
        &mut self,
        ctx: &mut Ctx,
        (dir, fam, key): (Dir, &str, SExpr),
        ty: &PTy,
        out: &mut Vec<Stmt>,
    ) -> Built {
        if dir == Dir::Out {
            let value = self.port_value(ctx, ty)?;
            let entry = crate::program::hexpr(&HExpr::Entry(fam.to_owned(), key.clone()));
            self.add_root(&entry, entry_ty(ty));
            out.push(Stmt::Connect(Place::Entry(fam.to_owned(), key), value));
            note!(self, own_targets);
        } else if let PTy::Data(t) = ty {
            self.pool(ctx, HExpr::Entry(fam.to_owned(), key), t)?;
            note!(self, own_selects);
        }
        Ok(())
    }

    /// `input y: T as key;`, and its `:=` or its readable name.
    fn keyed(
        &mut self,
        ctx: &mut Ctx,
        m: &mut Module,
        dir: Dir,
        key: &Key,
        ty: &Ty,
        out: &mut Vec<Stmt>,
    ) -> Built {
        let y = m.names.fresh("Y");
        let public = match key {
            Key::Str(n) => {
                note!(self, as_strings);
                note!(self, as_core, CORE.contains(&n.as_str()));
                string(n)
            }
            Key::Scalar(n) => {
                note!(self, as_portkeys);
                SExpr::PortKey(Box::new(string(n)), false, Box::new(lit(0)))
            }
            Key::Join(fam, k) => {
                note!(self, as_joins);
                SExpr::PortKey(Box::new(string(fam)), true, Box::new(lit(*k)))
            }
        };
        let pty = PTy::Data(ty.clone());
        out.push(port(dir == Dir::Out, &y, None, Some(public), pty.clone()));
        if dir == Dir::Out {
            let value = self.port_value(ctx, &pty)?;
            out.push(Stmt::Connect(Place::Name(y), value));
            note!(self, own_targets);
        } else {
            self.pool(ctx, HExpr::Name(y), ty)?;
            note!(self, own_selects);
        }
        Ok(())
    }

    /// A loop of keyed ports with the computed names `"c" + str(j + first)`.
    fn keyed_loop(
        &mut self,
        ctx: &mut Ctx,
        m: &mut Module,
        dir: Dir,
        (first, count): (u32, u32),
        ty: &Ty,
        out: &mut Vec<Stmt>,
    ) -> Built {
        let binder = m.names.fresh("j");
        let y = m.names.fresh("Y");
        let pty = PTy::Data(ty.clone());
        let public = computed_name(&binder, first);
        let mut body = vec![port(dir == Dir::Out, &y, None, Some(public), pty.clone())];
        note!(self, as_computed);
        let acc = if dir == Dir::Out {
            let value = self.port_value(ctx, &pty)?;
            body.push(Stmt::Connect(Place::Name(y), value));
            note!(self, own_targets);
            None
        } else {
            let g = Self::accumulator(&mut m.names, ty, out);
            body.push(Self::fold_in(&g, ty, HExpr::Name(y)));
            Some(g)
        };
        out.push(Stmt::For(binder, lit(0), lit(count), body));
        if let Some(g) = acc {
            self.pool(ctx, HExpr::Name(g), ty)?;
            note!(self, own_selects);
        }
        Ok(())
    }

    /// `let l = HP(name);`, or `let l = HP(0); let l = HP(1);` and so on.
    fn helper_calls(
        &mut self,
        ctx: &mut Ctx,
        m: &mut Module,
        (helper, first, calls): (usize, u32, u32),
        out: &mut Vec<Stmt>,
    ) -> Built {
        let Some(h) = self.port_helpers.get(helper).cloned() else {
            return Err(Fault::Type);
        };
        self.port_helper_used.insert(helper);
        for k in 0..calls {
            let arg = match &h.kind {
                HelperKind::Name => {
                    note!(self, helper_names);
                    // The name is a literal, or a concatenation of the
                    // grammar that the twin folds.
                    if self.tape.flag() {
                        string(&format!("c{first}"))
                    } else {
                        bin(SBin::Add, string("c"), SExpr::StrOf(Box::new(lit(first))))
                    }
                }
                HelperKind::Family(_) => {
                    note!(self, helper_families);
                    note!(self, helper_chains, k > 0);
                    lit(k)
                }
            };
            let l = m.names.fresh("l");
            out.push(Stmt::Let {
                name: l.clone(),
                mutable: false,
                ty: None,
                value: HExpr::Call(h.name.clone(), vec![HExpr::Static(arg)]),
            });
            self.pool(ctx, HExpr::Name(l), &h.ty)?;
        }
        Ok(())
    }

    /// The ports of the child that the parent binds: the input entries and
    /// the keyed inputs of its plan, each once.
    pub(super) fn bind_child_ports(
        &mut self,
        ctx: &Ctx,
        child: &Child,
        out: &mut Vec<Stmt>,
    ) -> Built {
        let declared = child.sig.plan.declared(&self.port_helpers);
        self.on_port(|b| {
            for d in declared.iter().filter(|d| d.dir == Dir::In) {
                let value = match &d.ty {
                    PTy::Unit => HExpr::Unit,
                    PTy::Data(t) => {
                        let types = b.types(t, &child.envs)?;
                        let want = Want { types, ty: None };
                        b.driver_at(&ctx.port_view(), &want, PORT_DEPTH)
                    }
                };
                let place = Builder::input_place(child, &d.public.base, d.public.key.map(lit));
                out.push(Stmt::Connect(place, value));
                note!(b, child_binds);
            }
            Ok(())
        })
    }

    /// The output entries and keyed outputs of the child, read into the
    /// pool by a `let` each, after all its inputs have a binding.
    pub(super) fn read_child_ports(
        &mut self,
        ctx: &mut Ctx,
        m: &mut Module,
        child: &Child,
        out: &mut Vec<Stmt>,
    ) -> Built {
        let declared = child.sig.plan.declared(&self.port_helpers);
        for d in declared.iter().filter(|d| d.dir == Dir::Out) {
            let PTy::Data(t) = &d.ty else {
                continue;
            };
            let expr = match d.public.key {
                Some(k) => HExpr::ChildEntry(
                    Box::new(HExpr::Name(child.name.clone())),
                    d.public.base.clone(),
                    lit(k),
                ),
                None => HExpr::Field(child.name.clone(), d.public.base.clone()),
            };
            let types = self.types(t, &child.envs)?;
            let l = m.names.fresh("l");
            out.push(Stmt::Let {
                name: l.clone(),
                mutable: false,
                ty: None,
                value: expr,
            });
            ctx.child_reads.insert(ctx.port.len());
            ctx.port.push(Hw {
                expr: HExpr::Name(l),
                ty: None,
                types,
                mutable: false,
            });
        }
        Ok(())
    }

    /// The value `e` of an output of the wanted type with each name of the
    /// pool mixed in: `read ^ e`, or `read != e` for a `Bool`. Each name
    /// reaches the first output that its type converts to, starting at the
    /// output that the port tape picks, so that every entry and keyed input
    /// of the module reaches an output.
    pub(super) fn mix_port(&mut self, ctx: &Ctx, outputs: &mut [(String, Want, HExpr)]) {
        if ctx.port.is_empty() || outputs.is_empty() {
            return;
        }
        self.on_port(|b| {
            let start = b.tape.index(outputs.len());
            for (i, h) in ctx.port.iter().enumerate() {
                let mixed = (0..outputs.len()).find_map(|d| {
                    let at = (start + i + d) % outputs.len();
                    let (_, want, _) = outputs.get(at)?;
                    adapt(h.expr.clone(), &Want::of(h), want).map(|read| (at, read))
                });
                let Some((at, read)) = mixed else {
                    note!(b, port_lost);
                    continue;
                };
                let Some((_, want, value)) = outputs.get_mut(at) else {
                    continue;
                };
                let op = if want.types.first() == Some(&Scalar::Bool) {
                    HBin::Ne
                } else {
                    HBin::Xor
                };
                let old = std::mem::replace(value, HExpr::Unit);
                *value = HExpr::Binary(op, Box::new(read), Box::new(old));
                note!(b, port_reaches);
                note!(b, child_reads, ctx.child_reads.contains(&i));
                #[cfg(test)]
                b.note_temp(&h.expr);
            }
        });
    }
}
