//! Each lowered random design parses with `circt-opt`.

use std::io::Write;
use std::process::{Command, Stdio};

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
        let mut child = Command::new("circt-opt")
            .stdin(Stdio::piped())
            .stdout(Stdio::null())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| TestCaseError::fail(format!("circt-opt: {e}")))?;
        if let Some(mut pipe) = child.stdin.take() {
            pipe.write_all(mlir.as_bytes()).map_err(|e| TestCaseError::fail(e.to_string()))?;
        }
        let out = child.wait_with_output().map_err(|e| TestCaseError::fail(e.to_string()))?;
        prop_assert!(out.status.success(), "{}\n{mlir}", String::from_utf8_lossy(&out.stderr));
    }
}
