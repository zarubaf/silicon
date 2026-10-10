//! The elaborator of the Silicon front end: the static values, the static evaluator with the
//! budgets and the cost model, and the digest names. See [the front end
//! design](../../doc/design/2026-10-09-frontend.md), sections 4.4, 4.5, and 5.

pub mod int;
pub mod sha256;
pub mod value;
