//! Functional surface language.
//!
//! This module is intentionally independent from the cubical core. Parsing and
//! elaboration will live here while the existing kernel remains the trusted
//! target language.

pub mod ast;
mod elaborate;
pub mod parser;

pub(crate) fn elaborate(program: &ast::Program) -> crate::Result<crate::syntax::Program> {
    elaborate::elaborate(program)
}
