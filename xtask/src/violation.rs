use std::fmt;
use std::path::PathBuf;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error,
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "the first warning-level check constructs it")
    )]
    Warning,
}

impl Severity {
    /// Errors fail the run. Warnings print only.
    pub fn fails_run(self) -> bool {
        match self {
            Self::Error => true,
            Self::Warning => false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Violation {
    pub path: PathBuf,
    pub line: Option<usize>,
    pub rule: &'static str,
    pub severity: Severity,
    pub message: String,
}

impl fmt::Display for Violation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.path.display())?;
        if let Some(line) = self.line {
            write!(f, ":{line}")?;
        }
        write!(f, ": [{}] {}", self.rule, self.message)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn displays_path_line_rule_message() {
        let v = Violation {
            path: PathBuf::from("a/b.rs"),
            line: Some(3),
            rule: "r",
            severity: Severity::Error,
            message: "bad".into(),
        };
        assert_eq!(v.to_string(), "a/b.rs:3: [r] bad");
    }

    #[test]
    fn displays_without_line() {
        let v = Violation {
            path: PathBuf::from("a"),
            line: None,
            rule: "r",
            severity: Severity::Warning,
            message: "m".into(),
        };
        assert_eq!(v.to_string(), "a: [r] m");
    }
}
