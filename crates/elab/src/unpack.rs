// SPDX-License-Identifier: Apache-2.0
//! The static unpack of section 7.4: the value of a hardware data type that the bits of a
//! payload hold. It reads each leaf at the offset that the pack of the payload gives, the first
//! leaf in the low bits, and it makes one value for each part of the type. A leaf of `w` bits
//! takes `w / 32 + 1` steps, so the work is the size of the zero value of the type, which the
//! caller charged before it. The walk keeps its own stack, so a type of any depth is safe on any
//! stack.

use crate::int::{read_bits, word_bit};
use crate::types::{Ty, TyId, Types};
use crate::value::Value;

/// A step of the walk: visit a part, or make a container of the last `n` values.
enum Step {
    Visit(TyId, u64),
    Array(TyId, usize),
    Tuple(usize),
    Record(TyId, usize),
}

/// The value of the type `t` that the little-endian words `words` hold from the bit `off`, or
/// `None` if `t` is not hardware data.
pub(crate) fn unpack(tys: &Types, words: &[u64], t: TyId, off: u64) -> Option<Value> {
    let mut done: Vec<Value> = Vec::new();
    let mut work = vec![Step::Visit(t, off)];
    while let Some(step) = work.pop() {
        #[cfg(test)]
        if matches!(step, Step::Visit(..)) {
            crate::counters::add(crate::counters::Count::Unpacked, 1);
        }
        match step {
            Step::Visit(t, off) => {
                match tys.get(t) {
                    Ty::Bool => done.push(Value::Bool(word_bit(words, off))),
                    Ty::UInt(w) => done.push(Value::UInt(read_bits(words, off, *w)?)),
                    Ty::SInt(w) => done.push(Value::SInt(read_bits(words, off, *w)?)),
                    Ty::Unit => done.push(Value::Unit),
                    Ty::Array(elem, len) => {
                        let n = usize::try_from(len.to_u64()?).ok()?;
                        work.push(Step::Array(*elem, n));
                        if n > 0 {
                            // An empty array reads no element, so the width of its element
                            // type, which can exceed `u64`, is never needed (Lean `Value.unpack`).
                            let width = tys.meta(*elem).width.to_u64()?;
                            work.extend((0..n as u64).rev().map(|k| {
                                Step::Visit(*elem, off.saturating_add(k.saturating_mul(width)))
                            }));
                        }
                    }
                    Ty::Tuple(parts) => {
                        work.push(Step::Tuple(parts.len()));
                        work.extend(parts.iter().enumerate().rev().map(|(k, part)| {
                            Step::Visit(*part, off.saturating_add(tys.offset(t, k as u64)))
                        }));
                    }
                    Ty::Struct(_) => {
                        let fields = tys.parts(t)?.types;
                        work.push(Step::Record(t, fields.len()));
                        work.extend(fields.iter().enumerate().rev().map(|(k, field)| {
                            Step::Visit(*field, off.saturating_add(tys.offset(t, k as u64)))
                        }));
                    }
                    Ty::Enum(_) => {
                        let widths = tys.widths(t)?;
                        let tag = read_bits(words, off, widths.tag)?;
                        let payload = (widths.payload > 0)
                            .then(|| {
                                read_bits(
                                    words,
                                    off.saturating_add(u64::from(widths.tag)),
                                    widths.payload,
                                )
                            })
                            .flatten();
                        done.push(Value::Enum(t, tag, payload));
                    }
                    Ty::Nat | Ty::Int | Ty::Type | Ty::String | Ty::List(_) | Ty::Fn(..) => {
                        return None;
                    }
                }
            }
            Step::Array(elem, n) => {
                let xs = done.split_off(done.len().checked_sub(n)?);
                done.push(Value::Array(elem, xs));
            }
            Step::Tuple(n) => {
                let xs = done.split_off(done.len().checked_sub(n)?);
                done.push(Value::tuple(xs));
            }
            Step::Record(t, n) => {
                let xs = done.split_off(done.len().checked_sub(n)?);
                done.push(Value::Record(t, xs));
            }
        }
    }
    done.pop()
}
