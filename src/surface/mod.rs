//! Functional surface language.
//!
//! This module is intentionally independent from the cubical core. Parsing and
//! elaboration will live here while the existing kernel remains the trusted
//! target language.

pub mod ast;
mod lower;
pub mod parser;

pub(crate) fn to_core_source(program: &ast::Program) -> crate::Result<String> {
    lower::to_core_source(program)
}
