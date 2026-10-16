// SPDX-License-Identifier: Apache-2.0
//! The fuel and the operations on static values, as the pure functions of Lean `Source.Eval`
//! define them. Each operation checks the types of its operands, then pays its charge, and
//! only then does its work. A type error thus costs no fuel, and a charge that the fuel cannot
//! pay stops the operation before it runs.

mod container;

pub(crate) use container::{
    common_of, common_ty, composite, container_op, container_ty, same_pair, scalar_join,
};
pub(crate) use container::{plan as plan_value, run as run_value};

use crate::Code;
use crate::int::Int;
use crate::limit;
use crate::types::{Ty, TyId, Types};
use crate::value::{Value, width_size};
use core_ir::{Bits, Pred};
use parse::ast::{BinOp, UnOp};
use resolve::Prelude;

/// An error without a position. The evaluator adds the position of its node.
pub(crate) type Fault = (Code, String);

/// The widest finite type.
pub(crate) const MAX_WIDTH: u64 = 65536;

/// The fuel that remains. A charge is a `u128`, so a sum or a product of two sizes is exact.
pub(crate) struct Fuel {
    left: u64,
}

impl Fuel {
    pub(crate) fn new(fuel: u64) -> Fuel {
        Fuel { left: fuel }
    }

    pub(crate) fn left(&self) -> u64 {
        self.left
    }

    /// Pays `units`, or gives `S015` and keeps the fuel.
    pub(crate) fn pay(&mut self, units: u128) -> Result<(), Fault> {
        match u64::try_from(units) {
            Ok(units) if units <= self.left => {
                self.left -= units;
                Ok(())
            }
            _ => Err(self.cannot_pay(&units.to_string())),
        }
    }

    /// Pays a charge of any size.
    pub(crate) fn pay_int(&mut self, units: &Int) -> Result<(), Fault> {
        match units.to_u64() {
            Some(units) => self.pay(u128::from(units)),
            None => Err(self.cannot_pay(&int_text(units))),
        }
    }

    /// Pays the units of a walk over the pairs of two types, or gives `S015` with a message that
    /// has no count. The walk stops when the fuel cannot pay it, so it does not know the whole
    /// count (design section 6.2). Lean prints the same text.
    pub(crate) fn pay_joins(&mut self, units: &Int) -> Result<(), Fault> {
        match units.to_u64() {
            Some(units) if units <= self.left => {
                self.left -= units;
                Ok(())
            }
            _ => Err((
                Code::S015,
                format!(
                    "the fuel cannot pay the joins of the types; {} remain; raise --fuel",
                    self.left
                ),
            )),
        }
    }

    /// Pays the units of the scan of a string, or gives `S015` with a message that has no count.
    /// A string that the fuel cannot pay is not counted (design section 6.2). Lean prints the
    /// same text.
    pub(crate) fn pay_scan(&mut self, units: u128) -> Result<(), Fault> {
        match u64::try_from(units) {
            Ok(units) if units <= self.left => {
                self.left -= units;
                Ok(())
            }
            _ => Err((
                Code::S015,
                format!(
                    "the fuel cannot pay the scan of the string; {} remain; raise --fuel",
                    self.left
                ),
            )),
        }
    }

    fn cannot_pay(&self, units: &str) -> Fault {
        (Code::S015, pay_text(units, self.left))
    }
}

/// The message of a charge of `units` when `left` units remain. Lean prints the same text.
pub(crate) fn pay_text(units: impl std::fmt::Display, left: u64) -> String {
    format!("the fuel cannot pay {units} unit(s); {left} remain; raise --fuel")
}

/// An integer in a message: decimal up to 256 bits, else its bit length. The bit length needs
/// no decimal conversion, so a message stays small and cheap for any computed integer.
pub(crate) fn int_text(n: &Int) -> String {
    let bits = n.log2() + 1;
    if bits <= 256 {
        n.to_string()
    } else if n.is_negative() {
        format!("a negative integer of {bits} bits")
    } else {
        format!("an integer of {bits} bits")
    }
}

/// A string in a message: at most 64 characters, then a note of the full length.
pub(crate) fn str_text(m: &str) -> String {
    match m.char_indices().nth(64) {
        None => m.to_owned(),
        Some((cut, _)) => format!("{}... ({} characters)", &m[..cut], m.chars().count()),
    }
}

pub(crate) fn unop_text(op: UnOp) -> &'static str {
    match op {
        UnOp::Not => "!",
        UnOp::Inv => "~",
        UnOp::Neg => "-",
    }
}

pub(crate) fn binop_text(op: BinOp) -> &'static str {
    match op {
        BinOp::Lor => "||",
        BinOp::Land => "&&",
        BinOp::Or => "|",
        BinOp::Xor => "^",
        BinOp::And => "&",
        BinOp::Eq => "==",
        BinOp::Ne => "!=",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        BinOp::Shl => "<<",
        BinOp::Shr => ">>",
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Addw => "+%",
        BinOp::Subw => "-%",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Rem => "%",
        BinOp::Mulw => "*%",
    }
}

fn type_error<T>(message: String) -> Result<T, Fault> {
    Err((Code::S010, message))
}

/// A bit vector whose value fits its width by construction.
fn bits(width: u32, value: Option<Bits>) -> Result<Bits, Fault> {
    value.ok_or_else(|| (Code::S012, format!("no value of {width} bits")))
}

/// The finite value of a signedness.
fn finite(signed: bool, x: Bits) -> Value {
    if signed {
        Value::SInt(x)
    } else {
        Value::UInt(x)
    }
}

/// Two finite operands of one type: the signedness and both bit vectors.
fn finite_pair<'a>(a: &'a Value, b: &'a Value) -> Option<(bool, &'a Bits, &'a Bits)> {
    match (a, b) {
        (Value::UInt(x), Value::UInt(y)) if x.width() == y.width() => Some((false, x, y)),
        (Value::SInt(x), Value::SInt(y)) if x.width() == y.width() => Some((true, x, y)),
        _ => None,
    }
}

fn sum(a: &Value, b: &Value) -> u128 {
    u128::from(a.size()) + u128::from(b.size())
}

fn product(a: &Value, b: &Value) -> u128 {
    u128::from(a.size()) * u128::from(b.size())
}

/// The range of a finite type, for the fit rule.
fn fits(t: &Ty, n: &Int) -> bool {
    match t {
        Ty::UInt(w) => n.fits_unsigned(u64::from(*w)),
        Ty::SInt(w) => n.fits_signed(u64::from(*w)),
        Ty::Nat => !n.is_negative(),
        _ => true,
    }
}

/// A typed use of `v` at the type `t`: the new value, or `None` if `v` itself is the result
/// with no charge. A static integer takes a finite type, and a container converts element by
/// element.
pub(crate) fn convert(
    t: TyId,
    v: &Value,
    fuel: &mut Fuel,
    tys: &Types,
) -> Result<Option<Value>, Fault> {
    match tys.get(t) {
        Ty::Unit | Ty::Array(..) | Ty::Tuple(_) | Ty::List(_) => {
            container::convert(t, v, fuel, tys)
        }
        Ty::Fn(..) => container::convert_fn(t, v, tys),
        scalar => container::convert_scalar(scalar, v, fuel, tys),
    }
}

pub(crate) fn unary(op: UnOp, a: &Value, fuel: &mut Fuel, tys: &Types) -> Result<Value, Fault> {
    let size = u128::from(a.size());
    match (op, a) {
        (UnOp::Not, Value::Bool(b)) => {
            fuel.pay(size)?;
            Ok(Value::Bool(!b))
        }
        (UnOp::Inv, Value::Int(n)) => {
            limit::capped(u128::from(n.bit_length()) + 1)?;
            fuel.pay(size)?;
            Ok(Value::Int(n.not()))
        }
        (UnOp::Neg, Value::Int(n)) => {
            fuel.pay(size)?;
            Ok(Value::Int(n.neg()))
        }
        (UnOp::Inv, Value::UInt(x) | Value::SInt(x)) => {
            fuel.pay(size)?;
            Ok(finite(matches!(a, Value::SInt(_)), x.not()))
        }
        (UnOp::Neg, Value::UInt(x) | Value::SInt(x)) => {
            fuel.pay(size)?;
            let zero = bits(x.width(), crate::int::finite(x.width(), 0))?;
            Ok(finite(matches!(a, Value::SInt(_)), zero.sub(x)))
        }
        _ => type_error(format!(
            "`{}` does not accept {}",
            unop_text(op),
            a.text(tys)
        )),
    }
}

/// The operators at which a static integer takes the finite type of the other operand.
pub(crate) fn unifies(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Addw
            | BinOp::Subw
            | BinOp::Mulw
            | BinOp::And
            | BinOp::Or
            | BinOp::Xor
            | BinOp::Eq
            | BinOp::Ne
            | BinOp::Lt
            | BinOp::Le
            | BinOp::Gt
            | BinOp::Ge
    )
}

/// A binary operator other than `&&` and `||`, after its operands and the typed uses.
pub(crate) fn binary(
    op: BinOp,
    a: &Value,
    b: &Value,
    fuel: &mut Fuel,
    tys: &Types,
) -> Result<Value, Fault> {
    let text = binop_text(op);
    match op {
        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
            if let (Value::Str(x), Value::Str(y)) = (a, b) {
                if op != BinOp::Add {
                    return type_error(format!("`{text}` does not accept strings; `+` joins them"));
                }
                limit::string(x.len() as u128 + y.len() as u128)?;
                fuel.pay(sum(a, b))?;
                return Ok(Value::Str(join(x, y)));
            }
            let (Value::Int(x), Value::Int(y)) = (a, b) else {
                return type_error(format!(
                    "`{text}` accepts only Int and Nat, not {} and {}",
                    a.text(tys),
                    b.text(tys)
                ));
            };
            limit::capped(limit::int_bound(op, x.bit_length(), y.bit_length()))?;
            let charge = if matches!(op, BinOp::Add | BinOp::Sub) {
                sum(a, b)
            } else {
                product(a, b)
            };
            fuel.pay(charge)?;
            int_arith(op, x, y)
        }
        BinOp::Addw | BinOp::Subw | BinOp::Mulw | BinOp::And | BinOp::Or | BinOp::Xor => {
            if let Some((signed, x, y)) = finite_pair(a, b) {
                fuel.pay(if op == BinOp::Mulw {
                    product(a, b)
                } else {
                    sum(a, b)
                })?;
                let r = match op {
                    BinOp::Addw => x.add(y),
                    BinOp::Subw => x.sub(y),
                    BinOp::Mulw => x.mul(y),
                    BinOp::And => x.and(y),
                    BinOp::Or => x.or(y),
                    _ => x.xor(y),
                };
                return Ok(finite(signed, r));
            }
            match (a, b) {
                (Value::Int(x), Value::Int(y)) => {
                    if !matches!(op, BinOp::And | BinOp::Or | BinOp::Xor) {
                        return type_error(format!("`{text}` needs a finite operand"));
                    }
                    limit::capped(limit::int_bound(op, x.bit_length(), y.bit_length()))?;
                    fuel.pay(sum(a, b))?;
                    Ok(Value::Int(match op {
                        BinOp::And => x.and(y),
                        BinOp::Or => x.or(y),
                        _ => x.xor(y),
                    }))
                }
                _ => type_error(format!(
                    "`{text}` needs integers of one type, not {} and {}",
                    a.text(tys),
                    b.text(tys)
                )),
            }
        }
        BinOp::Eq | BinOp::Ne => {
            equal_check(a, b, tys)?;
            fuel.pay(sum(a, b))?;
            Ok(Value::Bool((a == b) == (op == BinOp::Eq)))
        }
        BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
            if let (Value::Int(x), Value::Int(y)) = (a, b) {
                fuel.pay(sum(a, b))?;
                return Ok(Value::Bool(match op {
                    BinOp::Lt => x < y,
                    BinOp::Le => x <= y,
                    BinOp::Gt => x > y,
                    _ => x >= y,
                }));
            }
            let Some((signed, x, y)) = finite_pair(a, b) else {
                return type_error(format!(
                    "`{text}` orders integers of one type, not {} and {}",
                    a.text(tys),
                    b.text(tys)
                ));
            };
            fuel.pay(sum(a, b))?;
            let holds = x.icmp(pred(op, signed), y);
            Ok(Value::Bool(crate::int::bit(&holds, 0)))
        }
        BinOp::Shl | BinOp::Shr => shift(op, a, b, fuel, tys),
        BinOp::Land | BinOp::Lor => type_error(format!("`{text}` selects; it has no step")),
    }
}

/// The join of two strings: one new string, with no copy of either operand beyond the result.
fn join(x: &str, y: &str) -> String {
    #[cfg(test)]
    crate::counters::add(crate::counters::Count::Joined, (x.len() + y.len()) as u64);
    let mut joined = String::with_capacity(x.len() + y.len());
    joined.push_str(x);
    joined.push_str(y);
    joined
}

/// The type check of `==` on two scalars.
fn equal_check(a: &Value, b: &Value, tys: &Types) -> Result<(), Fault> {
    let same = matches!(
        (a, b),
        (Value::Int(_), Value::Int(_))
            | (Value::Bool(_), Value::Bool(_))
            | (Value::Str(_), Value::Str(_))
            | (Value::Type(_), Value::Type(_))
    ) || finite_pair(a, b).is_some();
    if same {
        Ok(())
    } else {
        type_error(format!(
            "`==` compares values of one type, not {} and {}",
            a.text(tys),
            b.text(tys)
        ))
    }
}

/// The ordinary operators on `Int`. They do not wrap.
fn int_arith(op: BinOp, x: &Int, y: &Int) -> Result<Value, Fault> {
    Ok(Value::Int(match op {
        BinOp::Add => x.add(y),
        BinOp::Sub => x.sub(y),
        BinOp::Mul => x.mul(y),
        BinOp::Div if y.is_zero() => return Err((Code::S013, "division by zero".to_owned())),
        BinOp::Div => x.tdiv(y),
        BinOp::Rem if y.is_zero() => {
            return Err((Code::S013, "remainder by zero".to_owned()));
        }
        _ => x.tmod(y),
    }))
}

/// The core predicate of an ordering, by signedness.
pub(crate) fn pred(op: BinOp, signed: bool) -> Pred {
    match (op, signed) {
        (BinOp::Lt, false) => Pred::Ult,
        (BinOp::Le, false) => Pred::Ule,
        (BinOp::Gt, false) => Pred::Ugt,
        (BinOp::Lt, true) => Pred::Slt,
        (BinOp::Le, true) => Pred::Sle,
        (BinOp::Gt, true) => Pred::Sgt,
        (_, true) => Pred::Sge,
        (_, false) => Pred::Uge,
    }
}

/// A shift count that is a static `Int` must not be negative.
fn nonnegative(k: &Int) -> Result<&Int, Fault> {
    if k.is_negative() {
        Err((
            Code::S013,
            format!("the shift count {} is negative", int_text(k)),
        ))
    } else {
        Ok(k)
    }
}

fn shift(op: BinOp, a: &Value, b: &Value, fuel: &mut Fuel, tys: &Types) -> Result<Value, Fault> {
    match a {
        Value::Int(x) => {
            let Value::Int(k) = b else {
                return type_error("an Int shift needs a static Int count".to_owned());
            };
            let k = nonnegative(k)?;
            if op == BinOp::Shl {
                limit::capped(limit::shl_bits(x, k))?;
                fuel.pay_int(&shl_size(x, k))?;
                Ok(int_shl(x, k))
            } else {
                fuel.pay(u128::from(a.size()))?;
                Ok(Value::Int(int_shr(x, k)))
            }
        }
        Value::UInt(x) | Value::SInt(x) => {
            let width = x.width();
            // The amount `min k w` fits `w` bits, because `w < 2^w`.
            let amount = match b {
                Value::Int(count) => nonnegative(count)?.to_u64().map_or(width, |count| {
                    u32::try_from(count.min(u64::from(width))).unwrap_or(width)
                }),
                Value::UInt(count) => crate::int::min_unsigned(count, width),
                _ => {
                    return type_error(format!(
                        "a shift count is UInt or a static Int, not {}",
                        b.text(tys)
                    ));
                }
            };
            fuel.pay(u128::from(width_size(width)))?;
            let amount = bits(width, crate::int::finite(width, u64::from(amount)))?;
            let signed = matches!(a, Value::SInt(_));
            Ok(finite(
                signed,
                match (op, signed) {
                    (BinOp::Shl, _) => x.shl(&amount),
                    (_, true) => x.shrs(&amount),
                    (_, false) => x.shru(&amount),
                },
            ))
        }
        _ => type_error(format!(
            "`{}` does not accept {}",
            binop_text(op),
            a.text(tys)
        )),
    }
}

/// The size of `a * 2^k`, from the bit length of `a`, before the shift runs.
fn shl_size(a: &Int, k: &Int) -> Int {
    if a.is_zero() {
        Int::from_u64(1)
    } else {
        Int::from_u64(a.log2())
            .add(k)
            .tdiv(&Int::from_u64(64))
            .add(&Int::from_u64(1))
    }
}

/// `a * 2^k` without the power `2^k`, after the size limit. A count above `u64` passed the
/// limit only with a zero operand, which makes no value at all, so the work stays in the charge
/// `shl_size a k`.
fn int_shl(a: &Int, k: &Int) -> Value {
    Value::Int(match k.to_u64() {
        Some(k) => a.shl(k),
        None => Int::zero(),
    })
}

/// `floor (a / 2^k)`. A count above the bit length gives 0 or -1 without a large shift.
fn int_shr(a: &Int, k: &Int) -> Int {
    match k.to_u64() {
        Some(k) if k <= a.log2() => a.shr(k),
        _ if a.is_negative() => Int::from_u64(1).neg(),
        _ => Int::zero(),
    }
}

/// `resize`: it keeps the signedness. A `UInt` fills with zeros and an `SInt` with its sign.
pub(crate) fn resize(t: TyId, v: &Value, fuel: &mut Fuel, tys: &Types) -> Result<Value, Fault> {
    let charge = |w: u32| u128::from(v.size()) + u128::from(width_size(w));
    match (tys.get(t), v) {
        (Ty::UInt(w), Value::UInt(x)) => {
            fuel.pay(charge(*w))?;
            Ok(Value::UInt(set_width(x, *w, false)?))
        }
        (Ty::SInt(w), Value::SInt(x)) => {
            fuel.pay(charge(*w))?;
            Ok(Value::SInt(set_width(x, *w, true)?))
        }
        _ => type_error(format!(
            "`resize` needs finite types of one signedness, not {}",
            v.text(tys)
        )),
    }
}

/// `setWidth` or `signExtend` of `x` to the width `w`.
fn set_width(x: &Bits, w: u32, sign_extend: bool) -> Result<Bits, Fault> {
    let u = x.width();
    if w <= u {
        return Ok(x.extract(0, w));
    }
    let fill = bits(w - u, crate::int::finite(w - u, 0))?;
    let fill = if sign_extend && crate::int::bit(x, u - 1) {
        fill.not()
    } else {
        fill
    };
    Ok(fill.concat(x))
}

/// `reinterpret`: it keeps the width and changes the signedness.
pub(crate) fn reinterpret(
    t: TyId,
    v: &Value,
    fuel: &mut Fuel,
    tys: &Types,
) -> Result<Value, Fault> {
    let t = tys.get(t);
    match (t, v) {
        (Ty::UInt(w) | Ty::SInt(w), Value::UInt(x) | Value::SInt(x)) => {
            if x.width() != *w {
                return type_error("`reinterpret` keeps the width".to_owned());
            }
            fuel.pay(u128::from(v.size()) + u128::from(width_size(*w)))?;
            Ok(finite(matches!(t, Ty::SInt(_)), x.clone()))
        }
        _ => type_error(format!(
            "`reinterpret` needs finite types, not {}",
            v.text(tys)
        )),
    }
}

/// `UInt[w]`, `SInt[w]`, or `List[T]`. The width is 1 to 65536.
pub(crate) fn family(k: Prelude, args: &[&Value], tys: &mut Types) -> Result<TyId, Fault> {
    match (k, args) {
        (Prelude::List, [Value::Type(e)]) => Ok(tys.list(*e)),
        (Prelude::List, [v]) => type_error(format!(
            "the element of a list is a type, not {}",
            v.text(tys)
        )),
        (Prelude::UInt | Prelude::SInt, [Value::Int(w)]) => {
            let width = w
                .to_u64()
                .filter(|w| (1..=MAX_WIDTH).contains(w))
                .and_then(|w| u32::try_from(w).ok());
            let Some(width) = width else {
                return Err((
                    Code::S012,
                    format!("the width {} is not 1 to 65536", int_text(w)),
                ));
            };
            Ok(tys.mk(if k == Prelude::UInt {
                Ty::UInt(width)
            } else {
                Ty::SInt(width)
            }))
        }
        (Prelude::UInt | Prelude::SInt, [v]) => {
            type_error(format!("a width is a static Int, not {}", v.text(tys)))
        }
        _ => Err((
            Code::S007,
            "a type family takes one index argument".to_owned(),
        )),
    }
}
