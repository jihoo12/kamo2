#![forbid(unsafe_code)]
//! Experimental Cartesian cubical kernel with checked univalence library terms.
//! See README.md and docs/rules.md for the implemented rules and limitations.
mod arena;
mod check;
mod eval;
mod face;
mod glue;
mod hash;
mod hit;
mod quote;
pub mod surface;
mod syntax;

use std::collections::HashSet;
use std::fmt;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};
pub type Result<T> = std::result::Result<T, Error>;
/// Bounds parser allocation; evaluation has separate work and arena budgets.
pub const MAX_SOURCE_BYTES: usize = 4 * 1024 * 1024;
const MAX_MODULE_IMPORT_DEPTH: usize = 64;
const MAX_IMPORTED_MODULES: usize = 1024;
const MAX_TRANSITIVE_SOURCE_BYTES: usize = 64 * 1024 * 1024;

#[derive(Clone, Debug)]
pub struct Error {
    pub offset: Option<usize>,
    pub message: String,
}
impl Error {
    fn at(offset: usize, message: impl Into<String>) -> Self {
        Self {
            offset: Some(offset),
            message: message.into(),
        }
    }
    fn plain(message: impl Into<String>) -> Self {
        Self {
            offset: None,
            message: message.into(),
        }
    }
    /// Byte offsets are rendered as one-based Unicode character columns.
    pub fn render(&self, file: &str, source: &str) -> String {
        if let Some(offset) = self.offset {
            let mut end = offset.min(source.len());
            while !source.is_char_boundary(end) {
                end -= 1;
            }
            let prefix = &source[..end];
            let line = prefix.bytes().filter(|b| *b == b'\n').count() + 1;
            let column = prefix.rsplit('\n').next().unwrap_or("").chars().count() + 1;
            format!("{file}:{line}:{column}: {}", self.message)
        } else {
            format!("{file}: {}", self.message)
        }
    }
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}
impl std::error::Error for Error {}

#[derive(Clone, Copy, Debug)]
pub struct Options {
    pub fuel: u64,
    pub optimized: bool,
    pub max_nodes: usize,
}
impl Default for Options {
    fn default() -> Self {
        Self {
            fuel: 1_000_000,
            optimized: true,
            max_nodes: 250_000,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct Statistics {
    pub steps: u64,
    pub value_nodes: usize,
    pub environment_nodes: usize,
    pub substitution_nodes: usize,
    pub face_nodes: usize,
    /// Peak retained arena capacities, including Vec payloads. Excludes hash maps,
    /// allocator metadata, syntax, stack, and temporary face-solver allocations.
    pub arena_bytes: usize,
    pub cache_entries: usize,
}
#[derive(Debug)]
pub struct NormalForm {
    pub text: String,
    pub statistics: Statistics,
}

/// Immutable checked syntax. Semantic IDs never cross this API boundary.
#[derive(Debug)]
pub struct CheckedProgram {
    program: syntax::Program,
}
impl CheckedProgram {
    pub fn check(source: &str) -> Result<Self> {
        Self::check_with(source, Options::default())
    }
    pub fn check_with(source: &str, options: Options) -> Result<Self> {
        if source.len() > MAX_SOURCE_BYTES {
            return Err(Error::plain("source size budget exceeded (maximum 4 MiB)"));
        }
        let program = syntax::parse(source)?;
        Self::check_program(program, options)
    }

    /// Parses the functional surface language, elaborates it to the existing
    /// core syntax, and checks the resulting program with the same kernel.
    pub fn check_surface(source: &str) -> Result<Self> {
        Self::check_surface_with(source, Options::default())
    }

    pub fn check_surface_with(source: &str, options: Options) -> Result<Self> {
        if source.len() > MAX_SOURCE_BYTES {
            return Err(Error::plain("source size budget exceeded (maximum 4 MiB)"));
        }
        let mut surface = surface::parser::parse(include_str!("../std/prelude.kamo"))?;
        let input = surface::parser::parse(source)?;
        surface.declarations.extend(input.declarations);
        let program = surface::elaborate(&surface)?;
        Self::check_program(program, options)
    }

    /// Loads a surface module and its transitive imports. An import `Foo.Bar`
    /// resolves to `Foo/Bar.kamo` relative to the importing file. Each module
    /// is elaborated once, before its importer.
    pub fn check_surface_file(path: impl AsRef<Path>) -> Result<Self> {
        Self::check_surface_file_with(path, Options::default())
    }

    pub fn check_surface_file_with(path: impl AsRef<Path>, options: Options) -> Result<Self> {
        fn visit(
            path: &Path,
            depth: usize,
            module_count: &mut usize,
            total_source_bytes: &mut usize,
            seen: &mut HashSet<PathBuf>,
            active: &mut HashSet<PathBuf>,
            items: &mut Vec<surface::ast::Item>,
        ) -> Result<()> {
            if depth >= MAX_MODULE_IMPORT_DEPTH {
                return Err(Error::plain("module import depth budget exceeded"));
            }
            let path = path
                .canonicalize()
                .map_err(|error| Error::plain(format!("{}: {error}", path.display())))?;
            if seen.contains(&path) {
                return Ok(());
            }
            if !active.insert(path.clone()) {
                return Err(Error::plain(format!(
                    "cyclic module import involving '{}'",
                    path.display()
                )));
            }
            if *module_count >= MAX_IMPORTED_MODULES {
                return Err(Error::plain("module count budget exceeded"));
            }
            *module_count += 1;
            let input = std::fs::File::open(&path)
                .map_err(|error| Error::plain(format!("{}: {error}", path.display())))?;
            // Bound allocation even for growing files and non-regular inputs.
            let mut bytes = Vec::new();
            let remaining = MAX_TRANSITIVE_SOURCE_BYTES.saturating_sub(*total_source_bytes);
            let limit = MAX_SOURCE_BYTES.min(remaining);
            input
                .take(limit as u64 + 1)
                .read_to_end(&mut bytes)
                .map_err(|error| Error::plain(format!("{}: {error}", path.display())))?;
            if bytes.len() > limit {
                let budget = if limit == MAX_SOURCE_BYTES {
                    "source size budget exceeded"
                } else {
                    "transitive source size budget exceeded"
                };
                return Err(Error::plain(format!("{}: {budget}", path.display())));
            }
            let source = String::from_utf8(bytes)
                .map_err(|error| Error::plain(format!("{}: {error}", path.display())))?;
            if source.len() > MAX_SOURCE_BYTES {
                return Err(Error::plain(format!(
                    "{}: source size budget exceeded",
                    path.display()
                )));
            }
            *total_source_bytes = total_source_bytes
                .checked_add(source.len())
                .ok_or_else(|| Error::plain("transitive source size budget exceeded"))?;
            if *total_source_bytes > MAX_TRANSITIVE_SOURCE_BYTES {
                return Err(Error::plain("transitive source size budget exceeded"));
            }
            let parsed = surface::parser::parse(&source)?;
            for import in &parsed.imports {
                if import == "Prelude" {
                    continue;
                }
                let relative = format!("{}.kamo", import.replace('.', "/"));
                visit(
                    &path.parent().unwrap_or(Path::new(".")).join(relative),
                    depth + 1,
                    module_count,
                    total_source_bytes,
                    seen,
                    active,
                    items,
                )?;
            }
            active.remove(&path);
            seen.insert(path);
            items.extend(parsed.declarations);
            Ok(())
        }

        let prelude = include_str!("../std/prelude.kamo");
        let mut surface = surface::parser::parse(prelude)?;
        let mut seen = HashSet::new();
        let mut active = HashSet::new();
        let mut module_count = 0;
        let mut total_source_bytes = prelude.len();
        visit(
            path.as_ref(),
            0,
            &mut module_count,
            &mut total_source_bytes,
            &mut seen,
            &mut active,
            &mut surface.declarations,
        )?;
        Self::check_program(surface::elaborate(&surface)?, options)
    }

    fn check_program(program: syntax::Program, options: Options) -> Result<Self> {
        program.validate_global_references()?;
        program.validate_scopes()?;
        program.validate_inductives()?;
        {
            let mut engine =
                eval::Engine::new(&program, options.optimized, options.fuel, options.max_nodes);
            engine.check_inductive_declarations()?;
        }
        for index in 0..program.decls.len() {
            let mut engine =
                eval::Engine::new(&program, options.optimized, options.fuel, options.max_nodes);
            engine.check_declaration(index)?;
        }
        Ok(Self { program })
    }
    pub fn names(&self) -> impl Iterator<Item = &str> {
        self.program.decls.iter().map(|d| d.name.as_str())
    }
    pub fn normalize(&self, name: &str) -> Result<NormalForm> {
        self.normalize_with(name, Options::default())
    }
    pub fn normalize_with(&self, name: &str, options: Options) -> Result<NormalForm> {
        let decl = self
            .program
            .decls
            .iter()
            .find(|d| d.name == name)
            .ok_or_else(|| Error::plain(format!("unknown declaration '{name}'")))?;
        let mut engine = eval::Engine::new(
            &self.program,
            options.optimized,
            options.fuel,
            options.max_nodes,
        );
        let env = engine.env(eval::Env::default());
        let face = engine.faces.top();
        let ty = engine.thunk(decl.ty, env);
        let body = engine.thunk(decl.body, env);
        let text = engine.quote(body, ty, face)?;
        Ok(NormalForm {
            text,
            statistics: engine.statistics(),
        })
    }
    /// Measures semantic conversion of two checked definitions, without parsing,
    /// checking, quotation, or output inside the timed section.
    pub fn benchmark_conversion(
        &self,
        left: &str,
        right: &str,
        options: Options,
    ) -> Result<(Duration, Statistics, bool)> {
        let lookup = |name: &str| {
            self.program
                .decls
                .iter()
                .find(|d| d.name == name)
                .ok_or_else(|| Error::plain(format!("unknown declaration '{name}'")))
        };
        let left = lookup(left)?;
        let right = lookup(right)?;
        let mut engine = eval::Engine::new(
            &self.program,
            options.optimized,
            options.fuel,
            options.max_nodes,
        );
        let env = engine.env(eval::Env::default());
        let face = engine.faces.top();
        let lt = engine.thunk(left.ty, env);
        let rt = engine.thunk(right.ty, env);
        let l = engine.thunk(left.body, env);
        let r = engine.thunk(right.body, env);
        if !engine.conv(lt, rt, None, face)? {
            return Err(Error::plain("benchmark definitions have different types"));
        }
        let start = Instant::now();
        let equal = engine.conv(l, r, Some(lt), face)?;
        let elapsed = start.elapsed();
        Ok((elapsed, engine.statistics(), equal))
    }
}

#[cfg(test)]
mod trust_boundary_tests {
    use super::*;
    use crate::arena::Key;

    #[test]
    fn forged_global_proofs_are_rejected_before_evaluation() {
        for optimized in [false, true] {
            for target in [0, 1, usize::MAX] {
                let mut program = syntax::parse(
                    "(def bad (Path i Bool true false) (path i true)) (def later Bool true)",
                )
                .unwrap();
                let reference = program.alloc(syntax::Term::Global(target), 0);
                program.decls[0].body = reference;
                let error = CheckedProgram::check_program(
                    program,
                    Options {
                        optimized,
                        ..Default::default()
                    },
                )
                .unwrap_err();
                assert!(error.message.contains("global reference"), "{error}");
            }
        }
    }

    #[test]
    fn forged_global_dependencies_in_types_and_nested_terms_are_rejected() {
        for in_type in [false, true] {
            let mut program = syntax::parse("(def first Bool true) (def later Bool true)").unwrap();
            let reference = program.alloc(syntax::Term::Global(1), 0);
            let nested = program.alloc(syntax::Term::Ann(reference, program.decls[0].ty), 0);
            if in_type {
                program.decls[0].ty = nested;
            } else {
                program.decls[0].body = nested;
            }
            assert!(program.validate_global_references().is_err());
        }
    }

    #[test]
    fn malformed_syntax_edges_and_roots_are_rejected() {
        let mut program = syntax::parse("(def first Bool true)").unwrap();
        let cyclic = program.alloc(
            syntax::Term::Suc(syntax::TermId::new(program.terms.len())),
            0,
        );
        program.decls[0].body = cyclic;
        assert!(program.validate_global_references().is_err());
        let mut program = syntax::parse("(def first Bool true)").unwrap();
        program.decls[0].body = syntax::TermId::new(usize::MAX);
        assert!(program.validate_global_references().is_err());
    }

    #[test]
    fn ordinary_backward_global_dependencies_remain_valid() {
        CheckedProgram::check("(def first Bool true) (def second Bool first)").unwrap();
        CheckedProgram::check_surface("def first : Bool = true def second : Bool = first").unwrap();
    }
}

#[cfg(test)]
mod metadata_boundary_tests {
    use super::*;
    use crate::arena::Key;
    fn raw() -> syntax::Program {
        let source = surface::parser::parse(
            "data A : Type where { a : Bool -> A } data B : Type where { b : Bool -> B }",
        )
        .unwrap();
        surface::elaborate(&source).unwrap()
    }
    #[test]
    fn mutually_negative_families_are_rejected_in_both_modes() {
        for optimized in [false, true] {
            let mut program = raw();
            let a = program.alloc(syntax::Term::Inductive(syntax::InductiveId::new(0)), 0);
            let b = program.alloc(syntax::Term::Inductive(syntax::InductiveId::new(1)), 0);
            let bool_ty = program.alloc(syntax::Term::Bool, 0);
            let negative = program.alloc(syntax::Term::Pi(a, bool_ty), 0);
            program.constructors[0].arguments[0].ty = b;
            program.constructors[1].arguments[0].ty = negative;
            let error = CheckedProgram::check_program(
                program,
                Options {
                    optimized,
                    ..Default::default()
                },
            )
            .unwrap_err();
            assert!(error.message.contains("earlier inductive"), "{error}");
        }
    }
    #[test]
    fn invalid_metadata_roots_return_errors() {
        for location in 0..4 {
            let mut program = raw();
            let bad = syntax::TermId::new(usize::MAX);
            match location {
                0 => program.constructors[0].arguments[0].ty = bad,
                1 => program.constructors[0].result_indices.push(bad),
                2 => program.inductives[0]
                    .parameters
                    .push(syntax::TelescopeEntry {
                        name: "x".into(),
                        ty: bad,
                    }),
                _ => program.inductives[0].indices.push(syntax::TelescopeEntry {
                    name: "x".into(),
                    ty: bad,
                }),
            }
            let error = CheckedProgram::check_program(program, Options::default()).unwrap_err();
            assert!(
                error.message.contains("metadata syntax reference"),
                "{error}"
            );
        }
    }
    #[test]
    fn invalid_semantic_table_references_return_errors() {
        for term in [
            syntax::Term::Inductive(syntax::InductiveId::new(usize::MAX)),
            syntax::Term::Constructor(syntax::ConstructorId::new(usize::MAX)),
        ] {
            let mut program = raw();
            program.alloc(term, 0);
            assert!(CheckedProgram::check_program(program, Options::default()).is_err());
        }
    }
    #[test]
    fn backward_family_dependencies_and_direct_recursion_remain_valid() {
        CheckedProgram::check_surface("data Earlier : Type where { earlier : Earlier } data Later : Type where { wrap : Earlier -> Later; step : Later -> Later }").unwrap();
    }
}

#[cfg(test)]
mod general_scope_boundary_tests {
    use super::*;
    use syntax::{D, F, Term};
    fn raw() -> syntax::Program {
        syntax::parse("(def p (Path i Bool true true) (path i true)) (def value Bool true)")
            .unwrap()
    }
    #[test]
    fn escaped_path_dimensions_return_errors_in_both_modes() {
        for optimized in [false, true] {
            for index in [0, usize::MAX] {
                let mut program = raw();
                let path = program.alloc(Term::Global(0), 0);
                program.decls[1].body = program.alloc(Term::PApp(path, D::Bound(index)), 0);
                let error = CheckedProgram::check_program(
                    program,
                    Options {
                        optimized,
                        ..Default::default()
                    },
                )
                .unwrap_err();
                assert!(error.message.contains("escaped dimension"), "{error}");
            }
        }
    }
    #[test]
    fn faces_and_composition_endpoints_do_not_bind_dimensions() {
        for variant in 0..5 {
            let mut program = raw();
            let ty = program.decls[1].ty;
            let value = program.decls[1].body;
            let face = F::And(Box::new(F::Top), Box::new(F::Eq(D::Bound(0), D::Zero)));
            let term = match variant {
                0 => Term::System(ty, vec![(face, value)]),
                1 => Term::Glue(ty, vec![(face, ty, value)]),
                2 => Term::GlueIntro(ty, value, vec![(face, value)]),
                3 => Term::Com {
                    family: ty,
                    from: D::Bound(0),
                    to: D::One,
                    cap: value,
                    tubes: vec![],
                },
                _ => Term::Com {
                    family: ty,
                    from: D::Zero,
                    to: D::One,
                    cap: value,
                    tubes: vec![(face, value)],
                },
            };
            program.decls[1].body = program.alloc(term, 0);
            let error = CheckedProgram::check_program(program, Options::default()).unwrap_err();
            assert!(error.message.contains("escaped dimension"), "{error}");
        }
    }
    #[test]
    fn path_endpoints_remain_outside_the_family_binder() {
        let mut program = raw();
        let path = program.alloc(Term::Global(0), 0);
        let bad_endpoint = program.alloc(Term::PApp(path, D::Bound(0)), 0);
        program.decls[1].ty = program.alloc(
            Term::Path(program.decls[1].ty, bad_endpoint, program.decls[1].body),
            0,
        );
        assert!(
            CheckedProgram::check_program(program, Options::default())
                .unwrap_err()
                .message
                .contains("escaped dimension")
        );
    }
    #[test]
    fn shared_nodes_are_checked_at_each_scope_root() {
        for index in [0, usize::MAX] {
            let mut program = raw();
            let variable = program.alloc(Term::Var(index), 0);
            program.alloc(Term::Lam(variable), 0);
            program.decls[1].body = variable;
            assert!(
                CheckedProgram::check_program(program, Options::default())
                    .unwrap_err()
                    .message
                    .contains("escaped term")
            );
        }
    }
    #[test]
    fn bound_dimensions_and_terms_remain_valid() {
        CheckedProgram::check("(def p (Path i Bool true true) (path i true)) (def eta (Path i Bool true true) (path i (at p i))) (def id (Pi x Bool Bool) (lam x x))").unwrap();
        CheckedProgram::check_surface(
            "def id (A : Type) (x : A) : A = x def p (x : Bool) : x == x = path i => x",
        )
        .unwrap();
    }
}
