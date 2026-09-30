//! Functional surface language.
//!
//! This module is intentionally independent from the cubical core. Parsing and
//! elaboration will live here while the existing kernel remains the trusted
//! target language.

pub mod ast;
mod lower;
pub mod parser;
