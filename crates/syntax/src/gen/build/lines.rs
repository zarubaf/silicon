// SPDX-License-Identifier: Apache-2.0
//! Random input lines for the top ports of a generated program. The map is
//! independent of `elab::vectors`, so that the oracle does not reuse the
//! code under test.

use crate::r#gen::in_line;
use crate::r#gen::program::{Ports, Scalar};
use num_bigint::{BigInt, BigUint};
use proptest::collection::vec;
use proptest::prelude::*;

/// `cycles` random `in=` lines for the top ports: the domain reset first for
/// a clocked top, with the bias of `core_ir::gen::resets`, then each input
/// in byte order.
pub fn lines(ports: &Ports, cycles: usize) -> impl Strategy<Value = Vec<String>> + use<> {
    let clocked = ports.clocked;
    let names: Vec<String> = ports.inputs.iter().map(|(n, _)| n.clone()).collect();
    let values: Vec<BoxedStrategy<String>> =
        ports.inputs.iter().map(|(_, t)| port_value(*t)).collect();
    (core_ir::r#gen::resets(cycles), vec(values, cycles)).prop_map(move |(resets, rows)| {
        resets
            .into_iter()
            .zip(rows)
            .map(|(reset, row)| in_line(clocked.then_some(reset), names.iter().zip(row)))
            .collect()
    })
}

/// A random value of a port type, in decimal.
fn port_value(t: Scalar) -> BoxedStrategy<String> {
    match t {
        Scalar::Bool => any::<bool>().prop_map(|b| b.to_string()).boxed(),
        Scalar::UInt(w) | Scalar::SInt(w) => {
            let signed = matches!(t, Scalar::SInt(_));
            vec(any::<u8>(), w.div_ceil(8) as usize)
                .prop_map(move |bytes| {
                    let bits = BigUint::from_bytes_le(&bytes) & ((BigUint::from(1u8) << w) - 1u8);
                    let mut v = BigInt::from(bits);
                    if signed && v >= BigInt::from(1) << (w - 1) {
                        v -= BigInt::from(1) << w;
                    }
                    v.to_string()
                })
                .boxed()
        }
    }
}
