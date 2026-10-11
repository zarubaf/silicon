// SPDX-License-Identifier: Apache-2.0
//! Each lowered random design parses with `circt-opt`.

mod common;

use backend_circt::lower;
use core_ir::check::check;
use core_ir::r#gen;
use proptest::prelude::*;

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 64,
        failure_persistence: None,
        ..ProptestConfig::default()
    })]

    #[test]
    fn each_generated_design_lowers_to_valid_mlir(d in r#gen::design()) {
        let design = check(&d).map_err(|e| TestCaseError::fail(e.to_string()))?;
        let mlir = lower(&design);
        let out = common::run("circt-opt", &[], &mlir).map_err(TestCaseError::fail)?;
        prop_assert!(out.status.success(), "{}\n{mlir}", String::from_utf8_lossy(&out.stderr));
    }
}
