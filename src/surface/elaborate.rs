use super::ast::{
    DataDeclaration, Declaration, Dimension, Expr, Face, Item, Pattern, Program as SurfaceProgram,
};
use crate::arena::Key;
use crate::hit::{
    BoundaryPiece, ConstructorRef, HigherConstructorDecl, HigherConstructorId,
    PartialConstructorBoundary,
};
use crate::syntax::{ConstructorId, D, F, FamilyConstructors, Program, Term, TermId};
use crate::{Error, Result};
use std::collections::{HashMap, HashSet};

pub(crate) fn elaborate(surface: &SurfaceProgram) -> Result<Program> {
    Elaborator::default().program(surface)
}

#[cfg(test)]
fn elaborate_into(core: Program, surface: &SurfaceProgram) -> Result<Program> {
    Elaborator {
        core,
        ..Elaborator::default()
    }
    .program(surface)
}

#[derive(Default)]
struct Elaborator {
    core: Program,
    globals: HashMap<String, usize>,
    global_types: HashMap<String, Expr>,
    locals: Vec<(String, Expr)>,
    dims: Vec<String>,
    fresh: usize,
    current_definition: Option<String>,
    recursive_calls: HashMap<String, (String, Vec<Expr>)>,
}

impl Elaborator {
    fn resolve_inductive(&self, name: &str) -> Result<crate::syntax::InductiveId> {
        let mut matches = self
            .core
            .inductives
            .iter()
            .filter(|inductive| inductive.name == name)
            .map(|inductive| inductive.id);
        let Some(inductive) = matches.next() else {
            return Err(Error::plain(format!("unknown inductive '{name}'")));
        };
        if matches.next().is_some() {
            return Err(Error::plain(format!("ambiguous inductive '{name}'")));
        }
        Ok(inductive)
    }

    fn resolve_point_constructor(&self, name: &str) -> Result<ConstructorId> {
        let mut matches = self
            .core
            .constructors
            .iter()
            .filter(|constructor| constructor.name == name)
            .map(|constructor| constructor.id);
        let Some(constructor) = matches.next() else {
            return Err(Error::plain(format!("unknown constructor '{name}'")));
        };
        if matches.next().is_some() {
            return Err(Error::plain(format!("ambiguous constructor '{name}'")));
        }
        Ok(constructor)
    }

    fn resolve_constructor(&self, name: &str) -> Result<ConstructorId> {
        let constructor = self.resolve_point_constructor(name)?;
        let owner = self.core.constructors[constructor.index()].inductive;
        self.core.inductives[owner.index()]
            .constructors
            .ordinary()?;
        Ok(constructor)
    }

    fn resolve_higher_constructor(&self, name: &str) -> Result<HigherConstructorId> {
        let mut matches = self
            .core
            .higher
            .iter()
            .filter(|constructor| constructor.name == name)
            .map(|constructor| constructor.id);
        let Some(constructor) = matches.next() else {
            return Err(Error::plain(format!("unknown higher constructor '{name}'")));
        };
        if matches.next().is_some() {
            return Err(Error::plain(format!(
                "ambiguous higher constructor '{name}'"
            )));
        }
        self.core.higher_constructor(constructor)?;
        Ok(constructor)
    }

    fn name_is_taken(&self, name: &str) -> bool {
        self.globals.contains_key(name)
            || self
                .core
                .inductives
                .iter()
                .any(|inductive| inductive.name == name)
            || self
                .core
                .constructors
                .iter()
                .any(|constructor| constructor.name == name)
            || self
                .core
                .higher
                .iter()
                .any(|constructor| constructor.name == name)
    }

    fn inductive_application(
        &self,
        expr: &Expr,
    ) -> Result<(crate::syntax::InductiveId, Vec<Expr>, Vec<Expr>)> {
        let mut head = expr;
        let mut arguments = Vec::new();
        while let Expr::Apply { function, argument } = head {
            arguments.push((**argument).clone());
            head = function;
        }
        arguments.reverse();

        let Expr::Name(name) = head else {
            return Err(Error::plain("match scrutinee is not an inductive family"));
        };
        let inductive = self
            .resolve_inductive(name)
            .map_err(|_| Error::plain("match scrutinee is not an inductive family"))?;
        let declaration = &self.core.inductives[inductive.index()];
        let expected = declaration.parameters.len() + declaration.indices.len();
        if arguments.len() != expected {
            return Err(Error::plain(format!(
                "inductive family '{}' expects {} arguments, found {}",
                declaration.name,
                expected,
                arguments.len()
            )));
        }
        let indices = arguments.split_off(declaration.parameters.len());
        Ok((inductive, arguments, indices))
    }

    fn validate_constructor_branches(
        &self,
        branches: &[super::ast::MatchBranch],
    ) -> Result<crate::syntax::InductiveId> {
        let mut family = None;
        let mut seen = HashSet::new();
        for branch in branches {
            let Pattern::Constructor { name, arguments } = &branch.pattern else {
                return Err(Error::plain("match branches must use constructor patterns"));
            };
            let constructor_id = self.resolve_constructor(name)?;
            let constructor = &self.core.constructors[constructor_id.index()];
            if arguments.len() != constructor.arguments.len() {
                return Err(Error::plain(format!(
                    "constructor '{}' expects {} pattern arguments, found {}",
                    name,
                    constructor.arguments.len(),
                    arguments.len()
                )));
            }
            match family {
                Some(inductive) if inductive != constructor.inductive => {
                    return Err(Error::plain(
                        "match branches must belong to the same inductive family",
                    ));
                }
                None => family = Some(constructor.inductive),
                _ => {}
            }
            if !seen.insert(constructor_id) {
                return Err(Error::plain(format!(
                    "duplicate match branch for constructor '{name}'"
                )));
            }
        }
        let family = family.ok_or_else(|| Error::plain("match must have at least one branch"))?;
        let inductive = &self.core.inductives[family.index()];
        if let Some(missing) = inductive
            .constructors
            .ordinary()?
            .iter()
            .find(|constructor| !seen.contains(constructor))
        {
            let name = &self.core.constructors[missing.index()].name;
            return Err(Error::plain(format!(
                "non-exhaustive match: missing constructor '{name}'"
            )));
        }
        Ok(family)
    }

    fn program(mut self, surface: &SurfaceProgram) -> Result<Program> {
        for item in &surface.declarations {
            match item {
                Item::Definition(declaration) => self.declaration(declaration)?,
                Item::Data(declaration) => self.data_declaration(declaration)?,
            }
        }
        Ok(self.core)
    }

    fn data_declaration(&mut self, data: &DataDeclaration) -> Result<()> {
        if self.name_is_taken(&data.name) {
            return Err(Error::plain(format!(
                "duplicate declaration '{}'",
                data.name
            )));
        }
        let saved = self.locals.len();
        let mut parameters = Vec::new();
        for (name, ty) in &data.parameters {
            parameters.push(crate::syntax::TelescopeEntry {
                name: name.clone(),
                ty: self.term(ty)?,
            });
            self.locals.push((name.clone(), ty.clone()));
        }
        let mut indices = Vec::new();
        for (name, ty) in &data.indices {
            indices.push(crate::syntax::TelescopeEntry {
                name: name.clone(),
                ty: self.term(ty)?,
            });
            self.locals.push((name.clone(), ty.clone()));
        }
        self.locals.truncate(saved + data.parameters.len());
        let inductive =
            self.core
                .push_inductive(data.name.clone(), data.universe, parameters, indices);

        for constructor in &data.constructors {
            if self.name_is_taken(&constructor.name) {
                self.locals.truncate(saved);
                return Err(Error::plain(format!(
                    "duplicate declaration or constructor name '{}'",
                    constructor.name
                )));
            }
            let mut arguments = Vec::new();
            let mut recursive_arguments = Vec::new();
            for (position, (name, ty)) in constructor.arguments.iter().enumerate() {
                if expression_head(ty) == Some(data.name.as_str()) {
                    recursive_arguments.push(position);
                }
                arguments.push(crate::syntax::TelescopeEntry {
                    name: name.clone(),
                    ty: self.term(ty)?,
                });
                self.locals.push((name.clone(), ty.clone()));
            }

            if let Expr::Equality { left, right } = &constructor.result {
                if !data.parameters.is_empty()
                    || !data.indices.is_empty()
                    || !constructor.arguments.is_empty()
                {
                    self.locals.truncate(saved);
                    return Err(Error::plain(
                        "surface higher constructors currently support only the unparameterized nullary Circle fragment",
                    ));
                }
                let left_term = self.term(left)?;
                let right_term = self.term(right)?;
                let (left_head, left_args) = application_spine(left);
                let (right_head, right_args) = application_spine(right);
                let left_id = self.resolve_point_constructor(&left_head)?;
                let right_id = self.resolve_point_constructor(&right_head)?;
                let left_point = &self.core.constructors[left_id.index()];
                let right_point = &self.core.constructors[right_id.index()];
                if left_point.inductive != inductive
                    || right_point.inductive != inductive
                    || !left_args.is_empty()
                    || !right_args.is_empty()
                    || left_id != right_id
                {
                    self.locals.truncate(saved);
                    return Err(Error::plain(
                        "surface Circle path constructor endpoints must be the same earlier nullary point",
                    ));
                }
                let members = match &self.core.inductives[inductive.index()].constructors {
                    FamilyConstructors::Ordinary(points) if points.as_slice() == [left_id] => {
                        vec![ConstructorRef::Point(left_id)]
                    }
                    _ => {
                        self.locals.truncate(saved);
                        return Err(Error::plain(
                            "surface Circle requires exactly one earlier point constructor",
                        ));
                    }
                };
                self.core.inductives[inductive.index()].constructors =
                    FamilyConstructors::Higher(members);
                let id = HigherConstructorId::new(self.core.higher.len());
                self.core.higher.push(HigherConstructorDecl {
                    id,
                    inductive,
                    name: constructor.name.clone(),
                    arguments: vec![],
                    dimensions: vec!["i".into()],
                    result_indices: vec![],
                    boundary: PartialConstructorBoundary {
                        pieces: vec![
                            BoundaryPiece {
                                face: F::Eq(D::Bound(0), D::Zero),
                                term: left_term,
                            },
                            BoundaryPiece {
                                face: F::Eq(D::Bound(0), D::One),
                                term: right_term,
                            },
                        ],
                    },
                });
                if let FamilyConstructors::Higher(members) =
                    &mut self.core.inductives[inductive.index()].constructors
                {
                    members.push(ConstructorRef::Higher(id));
                }
            } else {
                let (head, applied) = application_spine(&constructor.result);
                if head != data.name || applied.len() != data.parameters.len() + data.indices.len()
                {
                    self.locals.truncate(saved);
                    return Err(Error::plain(format!(
                        "constructor '{}' must return '{}' with all parameters and indices",
                        constructor.name, data.name
                    )));
                }
                for ((parameter, _), actual) in data.parameters.iter().zip(&applied) {
                    if actual != &Expr::Name(parameter.clone()) {
                        self.locals.truncate(saved);
                        return Err(Error::plain(format!(
                            "constructor '{}' changes data parameter '{}'",
                            constructor.name, parameter
                        )));
                    }
                }
                let result_indices = applied[data.parameters.len()..]
                    .iter()
                    .map(|index| self.term(index))
                    .collect::<Result<Vec<_>>>()?;
                self.core.push_constructor(
                    inductive,
                    constructor.name.clone(),
                    arguments,
                    result_indices,
                    recursive_arguments,
                );
            }
            self.locals.truncate(saved + data.parameters.len());
        }
        self.locals.truncate(saved);
        Ok(())
    }

    fn declaration(&mut self, declaration: &Declaration) -> Result<()> {
        if self.name_is_taken(&declaration.name) {
            return Err(Error::plain("duplicate or reserved declaration name"));
        }
        let ty_expr = declaration
            .ty
            .as_ref()
            .ok_or_else(|| Error::plain("surface definitions require a type annotation"))?;
        let ty = self.term(ty_expr)?;
        self.current_definition = Some(declaration.name.clone());
        let body = self.term_expected(&declaration.value, Some(ty_expr));
        self.current_definition = None;
        self.recursive_calls.clear();
        let body = body?;
        let index = self.core.decls.len();
        self.core.push_decl(declaration.name.clone(), ty, body);
        self.globals.insert(declaration.name.clone(), index);
        self.global_types
            .insert(declaration.name.clone(), ty_expr.clone());
        Ok(())
    }

    fn lambda_n(&mut self, mut body: TermId, count: usize) -> TermId {
        for _ in 0..count {
            body = self.core.alloc(Term::Lam(body), 0);
        }
        body
    }

    fn nested_branches(
        &mut self,
        branches: &[super::ast::MatchBranch],
    ) -> Result<Vec<super::ast::MatchBranch>> {
        let mut groups: Vec<(String, Vec<PatternRow>)> = Vec::new();
        for branch in branches {
            let Pattern::Constructor { name, arguments } = &branch.pattern else {
                return Err(Error::plain("match branches must use constructor patterns"));
            };
            let constructor = self.resolve_constructor(name)?;
            if arguments.len() != self.core.constructors[constructor.index()].arguments.len() {
                return Err(Error::plain("constructor pattern has incorrect arity"));
            }
            let mut seen = HashSet::new();
            validate_pattern_binders(&branch.pattern, &mut seen)?;
            // Nested eliminations have different motives from the outer function.
            // Do not reinterpret a recursive call using an unrelated inner IH.
            if let Some(name) = &self.current_definition
                && !pattern_binds(&branch.pattern, name)
                && substitute(&branch.body, name, &Expr::Name("<nested-recursion>".into()))
                    != branch.body
            {
                return Err(Error::plain(
                    "self recursion in nested-pattern matches is not supported; use flat patterns",
                ));
            }
            let row = (arguments.clone(), branch.body.clone());
            if let Some((_, rows)) = groups
                .iter_mut()
                .find(|(constructor, _)| constructor == name)
            {
                rows.push(row);
            } else {
                groups.push((name.clone(), vec![row]));
            }
        }
        let mut result = Vec::new();
        for (name, rows) in groups {
            let columns = (0..rows[0].0.len())
                .map(|_| self.fresh_name())
                .collect::<Vec<_>>();
            let body = self.pattern_tree(&columns, rows, 0)?;
            result.push(super::ast::MatchBranch {
                pattern: Pattern::Constructor {
                    name,
                    arguments: columns.into_iter().map(Pattern::Name).collect(),
                },
                body,
            });
        }
        Ok(result)
    }

    fn pattern_tree(
        &mut self,
        columns: &[String],
        rows: Vec<PatternRow>,
        depth: usize,
    ) -> Result<Expr> {
        if depth > 128 {
            return Err(Error::plain("nested pattern depth limit exceeded"));
        }
        let column = (0..columns.len()).find(|column| {
            rows.iter()
                .any(|(patterns, _)| matches!(patterns[*column], Pattern::Constructor { .. }))
        });
        let Some(column) = column else {
            if rows.len() != 1 {
                return Err(Error::plain("overlapping nested constructor patterns"));
            }
            let (patterns, mut body) = rows.into_iter().next().unwrap();
            for (pattern, name) in patterns.into_iter().zip(columns) {
                let Pattern::Name(binder) = pattern else {
                    unreachable!()
                };
                body = substitute(&body, &binder, &Expr::Name(name.clone()));
            }
            return Ok(body);
        };
        let mut groups: Vec<(String, Vec<PatternRow>)> = Vec::new();
        for (mut patterns, body) in rows {
            let Pattern::Constructor { name, arguments } = patterns.remove(column) else {
                return Err(Error::plain(
                    "mixed variable and constructor patterns overlap in a nested match",
                ));
            };
            let constructor = self.resolve_constructor(&name)?;
            if arguments.len() != self.core.constructors[constructor.index()].arguments.len() {
                return Err(Error::plain(
                    "nested constructor pattern has incorrect arity",
                ));
            }
            patterns.splice(column..column, arguments);
            if let Some((_, group)) = groups
                .iter_mut()
                .find(|(constructor, _)| constructor == &name)
            {
                group.push((patterns, body));
            } else {
                groups.push((name, vec![(patterns, body)]));
            }
        }
        let mut branches = Vec::new();
        for (name, rows) in groups {
            let constructor = self.resolve_constructor(&name)?;
            let names = (0..self.core.constructors[constructor.index()].arguments.len())
                .map(|_| self.fresh_name())
                .collect::<Vec<_>>();
            let mut inner_columns = columns.to_vec();
            inner_columns.splice(column..column + 1, names.clone());
            branches.push(super::ast::MatchBranch {
                pattern: Pattern::Constructor {
                    name,
                    arguments: names.into_iter().map(Pattern::Name).collect(),
                },
                body: self.pattern_tree(&inner_columns, rows, depth + 1)?,
            });
        }
        Ok(Expr::Match {
            scrutinee: Box::new(Expr::Name(columns[column].clone())),
            branches,
        })
    }

    // Reify the motive at the actual indices/value through a typed environment.
    // Core decoding freshens inner binders before inserting possibly open arguments.
    fn explicit_match_type(
        &mut self,
        scrutinee: &Expr,
        binders: &[String],
        result: &Expr,
    ) -> Result<Expr> {
        let scrutinee_ty = self.infer(scrutinee)?;
        let (family, parameters, indices) = self.inductive_application(&scrutinee_ty)?;
        let declaration = self.core.inductives[family.index()].clone();
        declaration.constructors.ordinary()?;
        if binders.len() != indices.len() + 1 {
            return Err(Error::plain(format!(
                "match motive expects {} binders (indices followed by scrutinee), found {}",
                indices.len() + 1,
                binders.len()
            )));
        }
        let mut seen = HashSet::new();
        let mut renamed = result.clone();
        let mut names = Vec::new();
        for binder in binders {
            if !seen.insert(binder) {
                return Err(Error::plain("duplicate match motive binder"));
            }
            let fresh = self.fresh_name();
            renamed = substitute(&renamed, binder, &Expr::Name(fresh.clone()));
            names.push(fresh);
        }
        let saved = self.locals.len();
        let inferred = (|| {
            let mut abstract_telescope = parameters.clone();
            let mut actual_telescope = parameters;
            let mut actual_env = self
                .locals
                .iter()
                .map(|(name, _)| Expr::Name(name.clone()))
                .collect::<Vec<_>>();
            for ((entry, name), actual) in declaration.indices.iter().zip(&names).zip(&indices) {
                let abstract_ty = self.surface_expr_in(entry.ty, &abstract_telescope)?;
                let actual_ty = self.surface_expr_in(entry.ty, &actual_telescope)?;
                self.locals.push((name.clone(), abstract_ty));
                abstract_telescope.push(Expr::Name(name.clone()));
                actual_telescope.push(actual.clone());
                actual_env.push(Expr::Annotation {
                    value: Box::new(actual.clone()),
                    ty: Box::new(actual_ty),
                });
            }
            let abstract_value_ty = apply_expr(Expr::Name(declaration.name), abstract_telescope);
            self.locals
                .push((names.last().unwrap().clone(), abstract_value_ty));
            actual_env.push(Expr::Annotation {
                value: Box::new(scrutinee.clone()),
                ty: Box::new(scrutinee_ty),
            });
            let result = self.term(&renamed)?;
            self.surface_expr_in(result, &actual_env)
        })();
        self.locals.truncate(saved);
        inferred
    }

    fn lower_match(
        &mut self,
        scrutinee: &Expr,
        branches: &[super::ast::MatchBranch],
        expected: &Expr,
        explicit: Option<(&[String], &Expr)>,
    ) -> Result<TermId> {
        let expanded;
        let branches = if branches
            .iter()
            .any(|branch| pattern_is_nested(&branch.pattern))
        {
            expanded = self.nested_branches(branches)?;
            expanded.as_slice()
        } else {
            branches
        };
        let inductive = self.validate_constructor_branches(branches)?;
        let scrutinee_ty = self.infer(scrutinee)?;
        let (scrutinee_family, parameter_exprs, index_exprs) =
            self.inductive_application(&scrutinee_ty)?;
        if inductive != scrutinee_family {
            return Err(Error::plain(
                "match branches do not belong to the scrutinee inductive family",
            ));
        }

        let declaration = self.core.inductives[inductive.index()].clone();
        let parameters = parameter_exprs
            .iter()
            .map(|parameter| self.term(parameter))
            .collect::<Result<Vec<_>>>()?;
        let indices = index_exprs
            .iter()
            .map(|index| self.term(index))
            .collect::<Result<Vec<_>>>()?;
        let scrutinee = self.term_expected(scrutinee, Some(&scrutinee_ty))?;

        // Resolve the result in the original scope first. Reify its free variables
        // through an environment that abstracts distinct local indices/value.
        // Non-variable or repeated indices remain fixed (no equation solving).
        let expected_term = self.term(expected)?;
        let mut result_env = self
            .locals
            .iter()
            .map(|(n, _)| Expr::Name(n.clone()))
            .collect::<Vec<_>>();
        let targets = indices
            .iter()
            .copied()
            .chain([scrutinee])
            .collect::<Vec<_>>();
        let motive_names = targets
            .iter()
            .map(|_| self.fresh_name())
            .collect::<Vec<_>>();
        for (target, name) in targets.iter().zip(&motive_names) {
            if let Term::Var(index) = self.core.terms.get(*target).term {
                let occurrences = targets.iter().filter(|other| {
                    matches!(self.core.terms.get(**other).term, Term::Var(i) if i == index)
                }).count();
                if occurrences == 1 {
                    let position = result_env.len() - 1 - index;
                    result_env[position] = Expr::Name(name.clone());
                }
            }
        }
        let result = match explicit {
            Some((binders, result)) => {
                if binders.len() != motive_names.len() {
                    return Err(Error::plain(format!(
                        "match motive expects {} binders (indices followed by scrutinee), found {}",
                        motive_names.len(),
                        binders.len()
                    )));
                }
                let mut seen = HashSet::new();
                let mut result = result.clone();
                for (binder, fresh) in binders.iter().zip(&motive_names) {
                    if !seen.insert(binder) {
                        return Err(Error::plain("duplicate match motive binder"));
                    }
                    result = substitute(&result, binder, &Expr::Name(fresh.clone()));
                }
                result
            }
            None => self.surface_expr_in(expected_term, &result_env)?,
        };
        let saved = self.locals.len();
        let mut telescope = parameter_exprs.clone();
        for (entry, name) in declaration.indices.iter().zip(&motive_names) {
            let ty = self.surface_expr_in(entry.ty, &telescope)?;
            self.locals.push((name.clone(), ty));
            telescope.push(Expr::Name(name.clone()));
        }
        let value_type = apply_expr(Expr::Name(declaration.name.clone()), telescope);
        self.locals
            .push((motive_names.last().unwrap().clone(), value_type));
        let motive_body = self.term(&result);
        let canonical = motive_body.and_then(|body| {
            let env = self
                .locals
                .iter()
                .map(|(name, _)| Expr::Name(name.clone()))
                .collect::<Vec<_>>();
            Ok((body, self.surface_expr_in(body, &env)?))
        });
        self.locals.truncate(saved);
        let (motive_body, result) = canonical?;
        let motive = self.lambda_n(motive_body, motive_names.len());

        let mut methods = Vec::with_capacity(declaration.constructors.ordinary()?.len());
        for constructor_id in declaration.constructors.ordinary()? {
            let constructor = self.core.constructors[constructor_id.index()].clone();
            let branch = branches
                .iter()
                .find(|branch| match &branch.pattern {
                    Pattern::Constructor { name, .. } => name == &constructor.name,
                    Pattern::Name(_) => false,
                })
                .ok_or_else(|| Error::plain("validated match branch disappeared"))?;
            let Pattern::Constructor { arguments, .. } = &branch.pattern else {
                unreachable!("validated constructor pattern");
            };

            let saved_calls = self.recursive_calls.clone();
            let mut pushed = 0;
            let mut metadata_env = parameter_exprs.clone();
            let mut branch_body = branch.body.clone();
            let mut seen = HashSet::new();
            for (argument_index, (argument, entry)) in
                arguments.iter().zip(&constructor.arguments).enumerate()
            {
                let Pattern::Name(source_name) = argument else {
                    return Err(Error::plain(
                        "nested constructor patterns are not supported yet",
                    ));
                };
                if !seen.insert(source_name) {
                    return Err(Error::plain("duplicate pattern argument"));
                }
                // Fresh names prevent pattern binders from capturing outer result
                // variables or parameters during motive instantiation.
                let name = self.fresh_name();
                let value = Expr::Name(name.clone());
                branch_body = substitute(&branch_body, source_name, &value);
                let ty = self.surface_expr_in(entry.ty, &metadata_env)?;
                self.locals.push((name.clone(), ty.clone()));
                metadata_env.push(value.clone());
                pushed += 1;
                if constructor.recursive_arguments.contains(&argument_index) {
                    let (recursive_family, mut recursive_parameters, recursive_indices) =
                        self.inductive_application(&ty)?;
                    if recursive_family != inductive {
                        return Err(Error::plain(
                            "recursive constructor argument belongs to the wrong family",
                        ));
                    }
                    let ih_type =
                        instantiate_result(&result, &motive_names, &recursive_indices, value);
                    recursive_parameters.extend(recursive_indices);
                    let ih = self.fresh_name();
                    self.locals.push((ih.clone(), ih_type));
                    self.recursive_calls
                        .insert(name, (ih, recursive_parameters));
                    pushed += 1;
                }
            }
            let result_indices = constructor
                .result_indices
                .iter()
                .map(|index| self.surface_expr_in(*index, &metadata_env))
                .collect::<Result<Vec<_>>>()?;
            let constructor_value = apply_expr(Expr::Name(constructor.name.clone()), metadata_env);
            let branch_expected =
                instantiate_result(&result, &motive_names, &result_indices, constructor_value);
            let body = self.term_expected(&branch_body, Some(&branch_expected));
            self.recursive_calls = saved_calls;
            self.locals.truncate(saved);
            methods.push(self.lambda_n(body?, pushed));
        }

        Ok(self.core.alloc(
            Term::Elim {
                inductive,
                parameters,
                motive,
                methods,
                indices,
                scrutinee,
            },
            0,
        ))
    }

    fn dimension(&self, dimension: &Dimension) -> Result<D> {
        match dimension {
            Dimension::Zero => Ok(D::Zero),
            Dimension::One => Ok(D::One),
            Dimension::Name(name) => self
                .dims
                .iter()
                .rev()
                .position(|n| n == name)
                .map(D::Bound)
                .ok_or_else(|| Error::plain(format!("unknown dimension '{name}'"))),
        }
    }

    fn surface_dimension(&self, dimension: D) -> Result<Dimension> {
        match dimension {
            D::Zero => Ok(Dimension::Zero),
            D::One => Ok(Dimension::One),
            D::Bound(index) => self
                .dims
                .iter()
                .rev()
                .nth(index)
                .cloned()
                .map(Dimension::Name)
                .ok_or_else(|| Error::plain("escaped dimension in surface type")),
        }
    }

    fn term(&mut self, expr: &Expr) -> Result<TermId> {
        self.term_expected(expr, None)
    }

    fn face(&self, face: &Face) -> Result<F> {
        Ok(match face {
            Face::Top => F::Top,
            Face::Bottom => F::Bot,
            Face::Equal(a, b) => F::Eq(self.dimension(a)?, self.dimension(b)?),
            Face::And(a, b) => F::And(Box::new(self.face(a)?), Box::new(self.face(b)?)),
            Face::Or(a, b) => F::Or(Box::new(self.face(a)?), Box::new(self.face(b)?)),
        })
    }

    fn term_expected(&mut self, expr: &Expr, expected: Option<&Expr>) -> Result<TermId> {
        let term = match expr {
            Expr::MatchReturn {
                scrutinee,
                binders,
                result,
                branches,
            } => {
                let inferred;
                let expected = match expected {
                    Some(expected) => expected,
                    None => {
                        inferred = self.explicit_match_type(scrutinee, binders, result)?;
                        &inferred
                    }
                };
                return self.lower_match(scrutinee, branches, expected, Some((binders, result)));
            }

            Expr::Glue { base, branches } => {
                let base_term = self.term(base)?;
                let mut data = Vec::new();
                for (face, ty, equivalence) in branches {
                    let face = self.face(face)?;
                    let ty_term = self.term(ty)?;
                    let expected = self.equivalence_type(ty, base);
                    let equivalence = self.term_expected(equivalence, Some(&expected))?;
                    data.push((face, ty_term, equivalence));
                }
                Term::Glue(base_term, data)
            }
            Expr::GlueIntro { ty, base, branches } => {
                let Expr::Glue {
                    base: base_ty,
                    branches: data,
                } = self.type_head(ty, 64)?
                else {
                    return Err(Error::plain("glue requires an explicit Glue type"));
                };
                let ty = self.term(ty)?;
                let base = self.term_expected(base, Some(&base_ty))?;
                let mut elements = Vec::new();
                for (face, body) in branches {
                    let expected = data
                        .iter()
                        .find(|(f, _, _)| f == face)
                        .or_else(|| {
                            data.first()
                                .filter(|(_, first, _)| data.iter().all(|(_, ty, _)| ty == first))
                        })
                        .map(|(_, ty, _)| ty);
                    elements.push((self.face(face)?, self.term_expected(body, expected)?));
                }
                Term::GlueIntro(ty, base, elements)
            }
            Expr::Unglue { ty, value } => {
                let ty_term = self.term(ty)?;
                let value = self.term_expected(value, Some(ty))?;
                Term::Unglue(ty_term, value)
            }

            Expr::Annotation { value, ty } => {
                let value = self.term_expected(value, Some(ty))?;
                Term::Ann(value, self.term(ty)?)
            }

            Expr::Sigma {
                parameter,
                domain,
                codomain,
            } => {
                let domain_term = self.term(domain)?;
                self.locals.push((parameter.clone(), (**domain).clone()));
                let codomain_term = self.term(codomain);
                self.locals.pop();
                Term::Sigma(domain_term, codomain_term?)
            }
            Expr::Pair { first, second } => {
                let expected = expected.map(|ty| self.type_head(ty, 64)).transpose()?;
                let Some(Expr::Sigma {
                    parameter,
                    domain,
                    codomain,
                }) = expected
                else {
                    return Err(Error::plain("pair requires an expected Sigma type"));
                };
                let first_term = self.term_expected(first, Some(&domain))?;
                let first_typed = Expr::Annotation {
                    value: first.clone(),
                    ty: domain.clone(),
                };
                let second_ty = substitute(&codomain, &parameter, &first_typed);
                let second_term = self.term_expected(second, Some(&second_ty))?;
                Term::Pair(first_term, second_term)
            }
            Expr::Fst(pair) => Term::Fst(self.term(pair)?),
            Expr::Snd(pair) => Term::Snd(self.term(pair)?),

            Expr::System { ty, branches } => {
                let ty_term = self.term(ty)?;
                let branches = branches
                    .iter()
                    .map(|(face, body)| Ok((self.face(face)?, self.term_expected(body, Some(ty))?)))
                    .collect::<Result<Vec<_>>>()?;
                Term::System(ty_term, branches)
            }

            Expr::Com {
                dimension,
                family,
                from,
                to,
                cap,
                tubes,
            } => {
                let from_term = self.dimension(from)?;
                let to_term = self.dimension(to)?;
                // Faces, endpoints and cap are outside the composition binder.
                let faces = tubes
                    .iter()
                    .map(|(face, _)| self.face(face))
                    .collect::<Result<Vec<_>>>()?;
                let fresh = self.fresh_name();
                let mut family = (**family).clone();
                rename_dimension(&mut family, dimension, &fresh);
                let source = instantiate_dimension(&family, &fresh, from);
                let cap = self.term_expected(cap, Some(&source))?;
                self.dims.push(fresh.clone());
                let lowered = (|| {
                    let family_term = self.term(&family)?;
                    let tubes = tubes
                        .iter()
                        .zip(faces)
                        .map(|((_, body), face)| {
                            let mut body = body.clone();
                            rename_dimension(&mut body, dimension, &fresh);
                            Ok((face, self.term_expected(&body, Some(&family))?))
                        })
                        .collect::<Result<Vec<_>>>()?;
                    Ok::<_, Error>((family_term, tubes))
                })();
                self.dims.pop();
                let (family, tubes) = lowered?;
                Term::Com {
                    family,
                    from: from_term,
                    to: to_term,
                    cap,
                    tubes,
                }
            }

            Expr::PathP {
                dimension,
                family,
                left,
                right,
            } => {
                let fresh = self.fresh_name();
                let mut family = (**family).clone();
                rename_dimension(&mut family, dimension, &fresh);
                self.dims.push(fresh.clone());
                let family_term = self.term(&family);
                self.dims.pop();
                let left_ty = instantiate_dimension(&family, &fresh, &Dimension::Zero);
                let right_ty = instantiate_dimension(&family, &fresh, &Dimension::One);
                let left = self.term_expected(left, Some(&left_ty))?;
                let right = self.term_expected(right, Some(&right_ty))?;
                Term::Path(family_term?, left, right)
            }
            Expr::Coe {
                dimension,
                family,
                from,
                to,
                cap,
            } => {
                // Endpoints and cap live outside the family binder, even when
                // an endpoint has the same spelling as that binder.
                let from_term = self.dimension(from)?;
                let to_term = self.dimension(to)?;
                let fresh = self.fresh_name();
                let mut family = (**family).clone();
                rename_dimension(&mut family, dimension, &fresh);
                self.dims.push(fresh.clone());
                let family_term = self.term(&family);
                self.dims.pop();
                let source = instantiate_dimension(&family, &fresh, from);
                let cap = self.term_expected(cap, Some(&source))?;
                Term::Com {
                    family: family_term?,
                    from: from_term,
                    to: to_term,
                    cap,
                    tubes: vec![],
                }
            }
            Expr::Name(name) => {
                if let Some(index) = self
                    .locals
                    .iter()
                    .rev()
                    .position(|(local, _)| local == name)
                {
                    Term::Var(index)
                } else if let Some(index) = self.globals.get(name) {
                    Term::Global(*index)
                } else if let Ok(inductive) = self.resolve_inductive(name) {
                    Term::Inductive(inductive)
                } else if let Ok(constructor) = self.resolve_point_constructor(name) {
                    Term::Constructor(constructor)
                } else if let Ok(constructor) = self.resolve_higher_constructor(name) {
                    let higher = self.core.higher[constructor.index()].clone();
                    let family = &self.core.inductives[higher.inductive.index()];
                    if !family.parameters.is_empty() || !higher.arguments.is_empty() {
                        return Err(Error::plain(
                            "surface higher-constructor terms currently support only nullary Circle",
                        ));
                    }
                    let body = self.core.alloc(
                        Term::HigherApp {
                            constructor,
                            parameters: vec![],
                            arguments: vec![],
                            dimensions: vec![D::Bound(0)],
                        },
                        0,
                    );
                    Term::PLam(body)
                } else if name == "Bool" {
                    Term::Bool
                } else if name == "true" {
                    Term::True
                } else if name == "false" {
                    Term::False
                } else if name == "Nat" {
                    Term::Nat
                } else if name == "zero" {
                    Term::Zero
                } else {
                    return Err(Error::plain(format!("unknown name '{name}'")));
                }
            }
            Expr::Equality { left, right } => {
                let family = self.infer(left)?;
                let left = self.term_expected(left, Some(&family))?;
                let right = self.term_expected(right, Some(&family))?;
                // Path's family has one extra dimension binder; endpoints do not.
                // Re-lower under that scope rather than reusing an unshifted term.
                let anonymous = self.fresh_name();
                self.dims.push(anonymous);
                let family = self.term(&family);
                self.dims.pop();
                Term::Path(family?, left, right)
            }
            Expr::PathLambda { dimension, body } => {
                let fresh = self.fresh_name();
                let body_expected = match expected {
                    Some(Expr::Equality { left, .. }) => Some(self.infer(left)?),
                    Some(Expr::PathP {
                        dimension, family, ..
                    }) => Some(instantiate_dimension(
                        family,
                        dimension,
                        &Dimension::Name(fresh.clone()),
                    )),
                    _ => None,
                };
                // Canonicalize the bound dimension before storing local types.
                // A later path binder with the same source name must not capture
                // references to this dimension in those types or expectations.
                let mut body = (**body).clone();
                rename_dimension(&mut body, dimension, &fresh);
                self.dims.push(fresh);
                let body = self.term_expected(&body, body_expected.as_ref());
                self.dims.pop();
                Term::PLam(body?)
            }
            Expr::PathApply { path, dimension } => {
                let dimension = self.dimension(dimension)?;
                if let Expr::Name(name) = path.as_ref()
                    && let Ok(constructor) = self.resolve_higher_constructor(name)
                {
                    let higher = self.core.higher[constructor.index()].clone();
                    let family = &self.core.inductives[higher.inductive.index()];
                    if !family.parameters.is_empty() || !higher.arguments.is_empty() {
                        return Err(Error::plain(
                            "surface higher-constructor application currently supports only nullary Circle",
                        ));
                    }
                    Term::HigherApp {
                        constructor,
                        parameters: vec![],
                        arguments: vec![],
                        dimensions: vec![dimension],
                    }
                } else {
                    Term::PApp(self.term(path)?, dimension)
                }
            }
            Expr::Universe(level) => Term::U(*level),
            Expr::Bool => Term::Bool,
            Expr::True => Term::True,
            Expr::False => Term::False,
            Expr::Nat => Term::Nat,
            Expr::Zero => Term::Zero,
            Expr::Suc(value) => {
                let value = self.term(value)?;
                Term::Suc(value)
            }
            Expr::Pi {
                parameter,
                domain,
                codomain,
            } => {
                let domain_term = self.term(domain)?;
                let binder = parameter.clone().unwrap_or_else(|| "_".to_owned());
                self.locals.push((binder, (**domain).clone()));
                let codomain_term = self.term(codomain);
                self.locals.pop();
                Term::Pi(domain_term, codomain_term?)
            }
            Expr::Lambda { parameter, body } => {
                let (parameter_ty, body_expected) = match expected {
                    Some(Expr::Pi {
                        parameter: binder,
                        domain,
                        codomain,
                    }) => {
                        let body_expected = binder
                            .as_deref()
                            .map(|binder| {
                                substitute(codomain, binder, &Expr::Name(parameter.clone()))
                            })
                            .unwrap_or_else(|| (**codomain).clone());
                        ((**domain).clone(), Some(body_expected))
                    }
                    _ => (Expr::Name("<unknown>".to_owned()), None),
                };
                self.locals.push((parameter.clone(), parameter_ty));
                let body = self.term_expected(body, body_expected.as_ref());
                self.locals.pop();
                Term::Lam(body?)
            }
            Expr::Apply { function, argument } => {
                if let Some(ih) = self.recursive_ih(expr)? {
                    let index = self
                        .locals
                        .iter()
                        .rev()
                        .position(|(local, _)| local == &ih)
                        .ok_or_else(|| Error::plain("recursive induction hypothesis escaped"))?;
                    Term::Var(index)
                } else {
                    let function_ty = self.infer(function).ok();
                    let function = self.term(function)?;
                    let argument = match function_ty.as_ref() {
                        Some(Expr::Pi { domain, .. }) => {
                            self.term_expected(argument, Some(domain))?
                        }
                        _ => self.term(argument)?,
                    };
                    Term::App(function, argument)
                }
            }
            Expr::Let { name, value, body } => {
                let value_ty = self.infer(value)?;
                let value_term = self.term(value)?;
                self.locals.push((name.clone(), value_ty.clone()));
                let body_ty = match expected {
                    Some(expected) => expected.clone(),
                    None => self.infer(body)?,
                };
                let body_term = self.term_expected(body, Some(&body_ty))?;
                let body_ty_term = self.term(&body_ty)?;
                self.locals.pop();
                let domain = self.term(&value_ty)?;
                let lambda = self.core.alloc(Term::Lam(body_term), 0);
                let pi = self.core.alloc(Term::Pi(domain, body_ty_term), 0);
                let annotated = self.core.alloc(Term::Ann(lambda, pi), 0);
                return Ok(self.core.alloc(Term::App(annotated, value_term), 0));
            }
            Expr::If { .. } => {
                return Err(Error::plain(
                    "surface if is reserved until motive synthesis is implemented",
                ));
            }
            Expr::Match {
                scrutinee,
                branches,
            } => {
                let expected = expected
                    .ok_or_else(|| Error::plain("cannot infer surface match result type yet"))?;
                return self.lower_match(scrutinee, branches, expected, None);
            }
        };
        Ok(self.core.alloc(term, 0))
    }

    fn infer_metadata_name(&mut self, name: &str) -> Result<Expr> {
        if let Ok(inductive) = self.resolve_inductive(name) {
            let declaration = &self.core.inductives[inductive.index()];
            let mut result = Expr::Universe(declaration.universe);
            for entry in declaration
                .indices
                .iter()
                .rev()
                .chain(declaration.parameters.iter().rev())
            {
                result = Expr::Pi {
                    parameter: Some(entry.name.clone()),
                    domain: Box::new(self.surface_type(entry.ty)?),
                    codomain: Box::new(result),
                };
            }
            return Ok(result);
        }
        if let Ok(constructor) = self.resolve_point_constructor(name) {
            let constructor = self.core.constructors[constructor.index()].clone();
            let family = self.core.inductives[constructor.inductive.index()].clone();
            let mut env = Vec::new();
            let mut binders = Vec::new();
            for entry in family.parameters.iter().chain(&constructor.arguments) {
                let ty = self.surface_expr_in(entry.ty, &env)?;
                let name = self.fresh_name();
                env.push(Expr::Name(name.clone()));
                binders.push((name, ty));
            }
            let mut arguments = env[..family.parameters.len()].to_vec();
            for index in &constructor.result_indices {
                arguments.push(self.surface_expr_in(*index, &env)?);
            }
            let mut result = apply_expr(Expr::Name(family.name), arguments);
            for (parameter, domain) in binders.into_iter().rev() {
                result = Expr::Pi {
                    parameter: Some(parameter),
                    domain: Box::new(domain),
                    codomain: Box::new(result),
                };
            }
            return Ok(result);
        }

        if let Ok(constructor) = self.resolve_higher_constructor(name) {
            let higher = self.core.higher[constructor.index()].clone();
            let family = self.core.inductives[higher.inductive.index()].clone();
            if family.parameters.is_empty()
                && family.indices.is_empty()
                && higher.arguments.is_empty()
                && higher.result_indices.is_empty()
                && higher.boundary.pieces.len() == 2
            {
                let mut left = None;
                let mut right = None;
                for piece in higher.boundary.pieces {
                    let endpoint = match piece.face {
                        F::Eq(D::Bound(0), D::Zero) | F::Eq(D::Zero, D::Bound(0)) => &mut left,
                        F::Eq(D::Bound(0), D::One) | F::Eq(D::One, D::Bound(0)) => &mut right,
                        _ => continue,
                    };
                    if let Term::Constructor(point) = self.core.terms.get(piece.term).term {
                        *endpoint = Some(Expr::Name(
                            self.core.constructors[point.index()].name.clone(),
                        ));
                    }
                }
                if let (Some(left), Some(right)) = (left, right) {
                    return Ok(Expr::Equality {
                        left: Box::new(left),
                        right: Box::new(right),
                    });
                }
            }
        }
        match name {
            "Bool" | "Nat" => return Ok(Expr::Universe(0)),
            "true" | "false" => return Ok(Expr::Name("Bool".to_owned())),
            "zero" => return Ok(Expr::Name("Nat".to_owned())),
            _ => {}
        }
        Err(Error::plain(format!("cannot infer type of '{name}'")))
    }

    // `=` cannot occur in a parsed source name.
    fn fresh_name(&mut self) -> String {
        let name = format!("<match={}>", self.fresh);
        self.fresh += 1;
        name
    }

    // Decode checked telescope syntax with actual parameter/argument expressions,
    // rather than substituting names or placeholder strings for parameters.
    fn surface_expr_in(&mut self, term: TermId, env: &[Expr]) -> Result<Expr> {
        match self.core.terms.get(term).term.clone() {
            Term::U(level) => Ok(Expr::Universe(level)),
            Term::Bool => Ok(Expr::Bool),
            Term::True => Ok(Expr::True),
            Term::False => Ok(Expr::False),
            Term::Nat => Ok(Expr::Nat),
            Term::Zero => Ok(Expr::Zero),
            Term::Suc(value) => Ok(Expr::Suc(Box::new(self.surface_expr_in(value, env)?))),
            Term::Global(index) => Ok(Expr::Name(self.core.decls[index].name.clone())),
            Term::Inductive(id) => Ok(Expr::Name(self.core.inductives[id.index()].name.clone())),
            Term::Constructor(id) => {
                Ok(Expr::Name(self.core.constructors[id.index()].name.clone()))
            }
            Term::Path(family, left, right) => {
                let dimension = self.fresh_name();
                self.dims.push(dimension.clone());
                let family = self.surface_expr_in(family, env);
                self.dims.pop();
                Ok(Expr::PathP {
                    dimension,
                    family: Box::new(family?),
                    left: Box::new(self.surface_expr_in(left, env)?),
                    right: Box::new(self.surface_expr_in(right, env)?),
                })
            }
            Term::PApp(path, dimension) => Ok(Expr::PathApply {
                path: Box::new(self.surface_expr_in(path, env)?),
                dimension: self.surface_dimension(dimension)?,
            }),
            Term::PLam(body) => {
                let dimension = self.fresh_name();
                self.dims.push(dimension.clone());
                let body = self.surface_expr_in(body, env);
                self.dims.pop();
                Ok(Expr::PathLambda {
                    dimension,
                    body: Box::new(body?),
                })
            }
            Term::App(function, argument) => {
                // Surface lets lower to an annotated lambda application.
                if let Term::Ann(lambda, _) = self.core.terms.get(function).term
                    && let Term::Lam(body) = self.core.terms.get(lambda).term
                {
                    let value = self.surface_expr_in(argument, env)?;
                    let name = self.fresh_name();
                    let mut inner = env.to_vec();
                    inner.push(Expr::Name(name.clone()));
                    return Ok(Expr::Let {
                        name,
                        value: Box::new(value),
                        body: Box::new(self.surface_expr_in(body, &inner)?),
                    });
                }
                Ok(Expr::Apply {
                    function: Box::new(self.surface_expr_in(function, env)?),
                    argument: Box::new(self.surface_expr_in(argument, env)?),
                })
            }
            Term::Lam(body) => {
                let name = self.fresh_name();
                let mut inner = env.to_vec();
                inner.push(Expr::Name(name.clone()));
                Ok(Expr::Lambda {
                    parameter: name,
                    body: Box::new(self.surface_expr_in(body, &inner)?),
                })
            }
            Term::Pi(domain, codomain) | Term::Sigma(domain, codomain) => {
                let domain = self.surface_expr_in(domain, env)?;
                let name = self.fresh_name();
                let mut inner = env.to_vec();
                inner.push(Expr::Name(name.clone()));
                let codomain = Box::new(self.surface_expr_in(codomain, &inner)?);
                let domain = Box::new(domain);
                Ok(
                    if matches!(self.core.terms.get(term).term, Term::Sigma(..)) {
                        Expr::Sigma {
                            parameter: name,
                            domain,
                            codomain,
                        }
                    } else {
                        Expr::Pi {
                            parameter: Some(name),
                            domain,
                            codomain,
                        }
                    },
                )
            }
            Term::Glue(base, branches) => {
                let base = Box::new(self.surface_expr_in(base, env)?);
                let branches = branches
                    .into_iter()
                    .map(|(face, ty, eq)| {
                        Ok((
                            self.surface_face(&face)?,
                            self.surface_expr_in(ty, env)?,
                            self.surface_expr_in(eq, env)?,
                        ))
                    })
                    .collect::<Result<Vec<_>>>()?;
                Ok(Expr::Glue { base, branches })
            }
            Term::Ann(value, ty) => Ok(Expr::Annotation {
                value: Box::new(self.surface_expr_in(value, env)?),
                ty: Box::new(self.surface_expr_in(ty, env)?),
            }),
            Term::Pair(first, second) => Ok(Expr::Pair {
                first: Box::new(self.surface_expr_in(first, env)?),
                second: Box::new(self.surface_expr_in(second, env)?),
            }),
            Term::Fst(pair) => Ok(Expr::Fst(Box::new(self.surface_expr_in(pair, env)?))),
            Term::Snd(pair) => Ok(Expr::Snd(Box::new(self.surface_expr_in(pair, env)?))),
            Term::Var(index) => env
                .iter()
                .rev()
                .nth(index)
                .cloned()
                .ok_or_else(|| Error::plain("inductive metadata contains an escaped variable")),
            _ => Err(Error::plain(
                "match result or metadata is not representable in surface syntax",
            )),
        }
    }

    fn surface_type(&self, term: TermId) -> Result<Expr> {
        match self.core.terms.get(term).term.clone() {
            Term::U(level) => Ok(Expr::Universe(level)),
            Term::Bool => Ok(Expr::Bool),
            Term::Nat => Ok(Expr::Nat),
            Term::Inductive(inductive) => Ok(Expr::Name(
                self.core.inductives[inductive.index()].name.clone(),
            )),
            Term::App(function, argument) => Ok(Expr::Apply {
                function: Box::new(self.surface_type(function)?),
                argument: Box::new(self.surface_type(argument)?),
            }),
            Term::Var(index) => self
                .locals
                .iter()
                .rev()
                .nth(index)
                .map(|(name, _)| Expr::Name(name.clone()))
                .ok_or_else(|| Error::plain("inductive metadata contains an escaped variable")),
            _ => Err(Error::plain(
                "inductive metadata type is not representable in surface syntax",
            )),
        }
    }

    fn recursive_ih(&self, expr: &Expr) -> Result<Option<String>> {
        let (head, arguments) = application_spine(expr);
        if self.current_definition.as_ref() != Some(&head) || arguments.is_empty() {
            return Ok(None);
        }
        let Some(Expr::Name(argument_name)) = arguments.last() else {
            return Err(Error::plain(
                "recursive calls must target a structural argument",
            ));
        };
        let (ih, expected_prefix) = self.recursive_calls.get(argument_name).ok_or_else(|| {
            Error::plain("recursive call is not on a structurally smaller argument")
        })?;
        if &arguments[..arguments.len() - 1] != expected_prefix {
            return Err(Error::plain(
                "recursive call parameters or indices do not match the recursive argument",
            ));
        }
        Ok(Some(ih.clone()))
    }

    fn infer(&mut self, expr: &Expr) -> Result<Expr> {
        if let Some(ih) = self.recursive_ih(expr)? {
            return self.infer(&Expr::Name(ih));
        }
        match expr {
            Expr::Glue { base, .. } => self.infer(base),
            Expr::GlueIntro { ty, .. } => Ok((**ty).clone()),
            Expr::Unglue { ty, .. } => match self.type_head(ty, 64)? {
                Expr::Glue { base, .. } => Ok(*base),
                _ => Err(Error::plain("unglue requires an explicit Glue type")),
            },

            Expr::Annotation { ty, .. } => Ok((**ty).clone()),
            Expr::Pair { .. } => Err(Error::plain(
                "cannot infer a pair; provide an expected Sigma type",
            )),
            Expr::Fst(pair) | Expr::Snd(pair) => {
                let ty = self.infer(pair)?;
                match self.type_head(&ty, 64)? {
                    Expr::Sigma {
                        parameter,
                        domain,
                        codomain,
                    } => {
                        if matches!(expr, Expr::Fst(_)) {
                            Ok(*domain)
                        } else {
                            Ok(substitute(&codomain, &parameter, &Expr::Fst(pair.clone())))
                        }
                    }
                    _ => Err(Error::plain("projection expects a known Sigma type")),
                }
            }

            Expr::System { ty, .. } => Ok((**ty).clone()),
            Expr::PathP {
                dimension, family, ..
            } => {
                let fresh = self.fresh_name();
                let mut family = (**family).clone();
                rename_dimension(&mut family, dimension, &fresh);
                self.dims.push(fresh);
                let sort = self.infer(&family);
                self.dims.pop();
                Ok(Expr::Universe(universe_level(&sort?)?))
            }
            Expr::Coe {
                dimension,
                family,
                from,
                to,
                ..
            }
            | Expr::Com {
                dimension,
                family,
                from,
                to,
                ..
            } => {
                self.dimension(from)?;
                self.dimension(to)?;
                Ok(instantiate_dimension(family, dimension, to))
            }
            Expr::Name(name) => self
                .locals
                .iter()
                .rev()
                .find(|(local, _)| local == name)
                .map(|(_, ty)| ty.clone())
                .or_else(|| self.global_types.get(name).cloned())
                .map(Ok)
                .unwrap_or_else(|| self.infer_metadata_name(name)),
            Expr::Equality { left, .. } => {
                let family = self.infer(left)?;
                self.infer(&family)
            }
            Expr::PathApply { path, dimension } => {
                self.dimension(dimension)?;
                match self.infer(path)? {
                    Expr::Equality { left, .. } => self.infer(&left),
                    Expr::PathP {
                        dimension: binder,
                        family,
                        ..
                    } => Ok(instantiate_dimension(&family, &binder, dimension)),
                    _ => Err(Error::plain("path application expects a known path type")),
                }
            }
            Expr::PathLambda { .. } => Err(Error::plain(
                "cannot infer a surface path abstraction; provide an expected path type",
            )),
            Expr::Universe(level) => level
                .checked_add(1)
                .map(Expr::Universe)
                .ok_or_else(|| Error::plain("universe level overflow")),
            Expr::Bool | Expr::Nat => Ok(Expr::Universe(0)),
            Expr::True | Expr::False => Ok(Expr::Bool),
            Expr::Zero | Expr::Suc(_) => Ok(Expr::Nat),
            Expr::Apply { function, argument } => match self.infer(function)? {
                Expr::Pi {
                    parameter,
                    codomain,
                    ..
                } => Ok(match parameter {
                    Some(parameter) => substitute(&codomain, &parameter, argument),
                    None => *codomain,
                }),
                _ => Err(Error::plain(
                    "cannot apply a non-function surface expression",
                )),
            },
            Expr::Let { name, value, body } => {
                let value_ty = self.infer(value)?;
                self.locals.push((name.clone(), value_ty));
                let ty = self.infer(body);
                self.locals.pop();
                Ok(substitute(&ty?, name, value))
            }
            Expr::Pi {
                parameter,
                domain,
                codomain,
            } => self.infer_telescope(parameter.as_deref().unwrap_or("_"), domain, codomain),
            Expr::Sigma {
                parameter,
                domain,
                codomain,
            } => self.infer_telescope(parameter, domain, codomain),
            Expr::Lambda { .. } => Err(Error::plain(
                "cannot infer an unannotated lambda in a let binding",
            )),
            Expr::If { .. } => Err(Error::plain("cannot infer surface if yet")),
            Expr::MatchReturn {
                scrutinee,
                binders,
                result,
                ..
            } => self.explicit_match_type(scrutinee, binders, result),
            Expr::Match { .. } => Err(Error::plain(
                "cannot infer surface match without an explicit return motive",
            )),
        }
    }

    fn surface_face(&self, face: &F) -> Result<Face> {
        Ok(match face {
            F::Top => Face::Top,
            F::Bot => Face::Bottom,
            F::Eq(a, b) => Face::Equal(self.surface_dimension(*a)?, self.surface_dimension(*b)?),
            F::And(a, b) => Face::And(
                Box::new(self.surface_face(a)?),
                Box::new(self.surface_face(b)?),
            ),
            F::Or(a, b) => Face::Or(
                Box::new(self.surface_face(a)?),
                Box::new(self.surface_face(b)?),
            ),
        })
    }

    // Mirror the existing kernel representation: a map with contractible fibers.
    // This is an elaboration hint; the kernel independently checks the witness.
    fn equivalence_type(&mut self, domain: &Expr, base: &Expr) -> Expr {
        let function = self.fresh_name();
        let target = self.fresh_name();
        let point = self.fresh_name();
        let center = self.fresh_name();
        let other = self.fresh_name();
        let fiber = Expr::Sigma {
            parameter: point.clone(),
            domain: Box::new(domain.clone()),
            codomain: Box::new(Expr::Equality {
                left: Box::new(apply_expr(
                    Expr::Name(function.clone()),
                    [Expr::Name(point)],
                )),
                right: Box::new(Expr::Name(target.clone())),
            }),
        };
        Expr::Sigma {
            parameter: function,
            domain: Box::new(Expr::Pi {
                parameter: None,
                domain: Box::new(domain.clone()),
                codomain: Box::new(base.clone()),
            }),
            codomain: Box::new(Expr::Pi {
                parameter: Some(target),
                domain: Box::new(base.clone()),
                codomain: Box::new(Expr::Sigma {
                    parameter: center.clone(),
                    domain: Box::new(fiber.clone()),
                    codomain: Box::new(Expr::Pi {
                        parameter: Some(other.clone()),
                        domain: Box::new(fiber),
                        codomain: Box::new(Expr::Equality {
                            left: Box::new(Expr::Name(center)),
                            right: Box::new(Expr::Name(other)),
                        }),
                    }),
                }),
            }),
        }
    }

    // Expose named type families without changing the kernel's conversion rules.
    // Decoding uses fresh binders before beta substitution to avoid capturing arguments.
    fn type_head(&mut self, expr: &Expr, fuel: usize) -> Result<Expr> {
        if fuel == 0 {
            return Err(Error::plain("surface type unfolding limit exceeded"));
        }
        match expr {
            Expr::Annotation { value, .. } => self.type_head(value, fuel - 1),
            Expr::Name(name) if !self.locals.iter().any(|(local, _)| local == name) => {
                if let Some(index) = self.globals.get(name).copied() {
                    let body = self.core.decls[index].body;
                    let body = self.surface_expr_in(body, &[])?;
                    self.type_head(&body, fuel - 1)
                } else {
                    Ok(expr.clone())
                }
            }
            Expr::Apply { function, argument } => match self.type_head(function, fuel - 1)? {
                Expr::Lambda { parameter, body } => {
                    self.type_head(&substitute(&body, &parameter, argument), fuel - 1)
                }
                function => Ok(Expr::Apply {
                    function: Box::new(function),
                    argument: argument.clone(),
                }),
            },
            _ => Ok(expr.clone()),
        }
    }

    fn infer_telescope(&mut self, parameter: &str, domain: &Expr, codomain: &Expr) -> Result<Expr> {
        let domain_level = universe_level(&self.infer(domain)?)?;
        self.locals.push((parameter.to_owned(), domain.clone()));
        // Retain the same metadata and dimension scope while extending
        // only the term context, rather than constructing a blank core.
        let codomain_ty = self.infer(codomain);
        self.locals.pop();
        let codomain_level = universe_level(&codomain_ty?)?;
        Ok(Expr::Universe(domain_level.max(codomain_level)))
    }
}

type PatternRow = (Vec<Pattern>, Expr);

fn pattern_is_nested(pattern: &Pattern) -> bool {
    matches!(pattern, Pattern::Constructor { arguments, .. } if arguments.iter().any(|argument| matches!(argument, Pattern::Constructor { .. })))
}

fn pattern_binds(pattern: &Pattern, name: &str) -> bool {
    match pattern {
        Pattern::Name(binder) => binder == name,
        Pattern::Constructor { arguments, .. } => arguments
            .iter()
            .any(|argument| pattern_binds(argument, name)),
    }
}

fn validate_pattern_binders(pattern: &Pattern, seen: &mut HashSet<String>) -> Result<()> {
    match pattern {
        Pattern::Name(name) if !seen.insert(name.clone()) => {
            return Err(Error::plain("duplicate pattern argument"));
        }
        Pattern::Constructor { arguments, .. } => {
            for argument in arguments {
                validate_pattern_binders(argument, seen)?;
            }
        }
        _ => {}
    }
    Ok(())
}

fn apply_expr(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments
        .into_iter()
        .fold(head, |function, argument| Expr::Apply {
            function: Box::new(function),
            argument: Box::new(argument),
        })
}

fn instantiate_result(result: &Expr, names: &[String], indices: &[Expr], value: Expr) -> Expr {
    names
        .iter()
        .zip(indices.iter().cloned().chain([value]))
        .fold(result.clone(), |result, (name, value)| {
            substitute(&result, name, &value)
        })
}

fn application_spine(expr: &Expr) -> (String, Vec<Expr>) {
    let mut cursor = expr;
    let mut arguments = Vec::new();
    while let Expr::Apply { function, argument } = cursor {
        arguments.push((**argument).clone());
        cursor = function;
    }
    arguments.reverse();
    (
        match cursor {
            Expr::Name(name) => name.clone(),
            _ => String::new(),
        },
        arguments,
    )
}

fn expression_head(expr: &Expr) -> Option<&str> {
    let mut cursor = expr;
    while let Expr::Apply { function, .. } = cursor {
        cursor = function;
    }
    match cursor {
        Expr::Name(name) => Some(name),
        _ => None,
    }
}

fn universe_level(expr: &Expr) -> Result<u32> {
    if let Expr::Universe(level) = expr {
        Ok(*level)
    } else {
        Err(Error::plain("expected a surface type"))
    }
}

// Rename only dimension occurrences bound by the surrounding path abstraction;
// term binders and names inhabit a separate namespace.
fn rename_dimension(expr: &mut Expr, old: &str, new: &str) {
    replace_dimension(expr, old, &Dimension::Name(new.to_owned()));
}

fn instantiate_dimension(expr: &Expr, binder: &str, value: &Dimension) -> Expr {
    let mut result = expr.clone();
    replace_dimension(&mut result, binder, value);
    result
}

fn replace_dimension(expr: &mut Expr, old: &str, new: &Dimension) {
    match expr {
        Expr::MatchReturn {
            scrutinee,
            result,
            branches,
            ..
        } => {
            replace_dimension(scrutinee, old, new);
            replace_dimension(result, old, new);
            for branch in branches {
                replace_dimension(&mut branch.body, old, new);
            }
        }

        Expr::Glue { base, branches } => {
            replace_dimension(base, old, new);
            for (face, ty, eq) in branches {
                replace_face(face, old, new);
                replace_dimension(ty, old, new);
                replace_dimension(eq, old, new);
            }
        }
        Expr::GlueIntro { ty, base, branches } => {
            replace_dimension(ty, old, new);
            replace_dimension(base, old, new);
            for (face, body) in branches {
                replace_face(face, old, new);
                replace_dimension(body, old, new);
            }
        }
        Expr::Unglue { ty, value } => {
            replace_dimension(ty, old, new);
            replace_dimension(value, old, new);
        }

        Expr::Annotation { value, ty } => {
            replace_dimension(value, old, new);
            replace_dimension(ty, old, new);
        }

        Expr::Sigma {
            domain, codomain, ..
        } => {
            replace_dimension(domain, old, new);
            replace_dimension(codomain, old, new);
        }
        Expr::Pair { first, second } => {
            replace_dimension(first, old, new);
            replace_dimension(second, old, new);
        }
        Expr::Fst(pair) | Expr::Snd(pair) => replace_dimension(pair, old, new),

        Expr::System { ty, branches } => {
            replace_dimension(ty, old, new);
            for (face, body) in branches {
                replace_face(face, old, new);
                replace_dimension(body, old, new);
            }
        }

        Expr::Com {
            dimension,
            family,
            from,
            to,
            cap,
            tubes,
        } => {
            if dimension != old {
                replace_dimension(family, old, new);
            }
            for endpoint in [from, to] {
                replace_dim(endpoint, old, new);
            }
            replace_dimension(cap, old, new);
            for (face, body) in tubes {
                replace_face(face, old, new);
                if dimension != old {
                    replace_dimension(body, old, new);
                }
            }
        }

        Expr::PathP {
            dimension,
            family,
            left,
            right,
        } => {
            if dimension != old {
                replace_dimension(family, old, new);
            }
            replace_dimension(left, old, new);
            replace_dimension(right, old, new);
        }
        Expr::Coe {
            dimension,
            family,
            from,
            to,
            cap,
        } => {
            if dimension != old {
                replace_dimension(family, old, new);
            }
            for endpoint in [from, to] {
                if matches!(endpoint, Dimension::Name(name) if name == old) {
                    *endpoint = new.clone();
                }
            }
            replace_dimension(cap, old, new);
        }
        Expr::PathApply { path, dimension } => {
            replace_dimension(path, old, new);
            if matches!(dimension, Dimension::Name(name) if name == old) {
                *dimension = new.clone();
            }
        }
        Expr::PathLambda { dimension, body } => {
            if dimension != old {
                replace_dimension(body, old, new);
            }
        }
        Expr::Equality { left, right } => {
            replace_dimension(left, old, new);
            replace_dimension(right, old, new);
        }
        Expr::Pi {
            domain, codomain, ..
        } => {
            replace_dimension(domain, old, new);
            replace_dimension(codomain, old, new);
        }
        Expr::Lambda { body, .. } | Expr::Suc(body) => replace_dimension(body, old, new),
        Expr::Apply { function, argument } => {
            replace_dimension(function, old, new);
            replace_dimension(argument, old, new);
        }
        Expr::Let { value, body, .. } => {
            replace_dimension(value, old, new);
            replace_dimension(body, old, new);
        }
        Expr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            replace_dimension(condition, old, new);
            replace_dimension(then_branch, old, new);
            replace_dimension(else_branch, old, new);
        }
        Expr::Match {
            scrutinee,
            branches,
        } => {
            replace_dimension(scrutinee, old, new);
            for branch in branches {
                replace_dimension(&mut branch.body, old, new);
            }
        }
        Expr::Name(_)
        | Expr::Universe(_)
        | Expr::Bool
        | Expr::True
        | Expr::False
        | Expr::Nat
        | Expr::Zero => {}
    }
}

fn substitute(expr: &Expr, name: &str, replacement: &Expr) -> Expr {
    match expr {
        Expr::MatchReturn {
            scrutinee,
            binders,
            result,
            branches,
        } => {
            let plain = substitute(
                &Expr::Match {
                    scrutinee: scrutinee.clone(),
                    branches: branches.clone(),
                },
                name,
                replacement,
            );
            let Expr::Match {
                scrutinee,
                branches,
            } = plain
            else {
                unreachable!()
            };
            Expr::MatchReturn {
                scrutinee,
                branches,
                binders: binders.clone(),
                result: if binders.iter().any(|binder| binder == name) {
                    result.clone()
                } else {
                    Box::new(substitute(result, name, replacement))
                },
            }
        }

        Expr::Glue { base, branches } => Expr::Glue {
            base: Box::new(substitute(base, name, replacement)),
            branches: branches
                .iter()
                .map(|(face, ty, eq)| {
                    (
                        face.clone(),
                        substitute(ty, name, replacement),
                        substitute(eq, name, replacement),
                    )
                })
                .collect(),
        },
        Expr::GlueIntro { ty, base, branches } => Expr::GlueIntro {
            ty: Box::new(substitute(ty, name, replacement)),
            base: Box::new(substitute(base, name, replacement)),
            branches: branches
                .iter()
                .map(|(face, body)| (face.clone(), substitute(body, name, replacement)))
                .collect(),
        },
        Expr::Unglue { ty, value } => Expr::Unglue {
            ty: Box::new(substitute(ty, name, replacement)),
            value: Box::new(substitute(value, name, replacement)),
        },

        Expr::Annotation { value, ty } => Expr::Annotation {
            value: Box::new(substitute(value, name, replacement)),
            ty: Box::new(substitute(ty, name, replacement)),
        },

        Expr::Sigma {
            parameter,
            domain,
            codomain,
        } => Expr::Sigma {
            parameter: parameter.clone(),
            domain: Box::new(substitute(domain, name, replacement)),
            codomain: if parameter == name {
                codomain.clone()
            } else {
                Box::new(substitute(codomain, name, replacement))
            },
        },
        Expr::Pair { first, second } => Expr::Pair {
            first: Box::new(substitute(first, name, replacement)),
            second: Box::new(substitute(second, name, replacement)),
        },
        Expr::Fst(pair) => Expr::Fst(Box::new(substitute(pair, name, replacement))),
        Expr::Snd(pair) => Expr::Snd(Box::new(substitute(pair, name, replacement))),

        Expr::System { ty, branches } => Expr::System {
            ty: Box::new(substitute(ty, name, replacement)),
            branches: branches
                .iter()
                .map(|(face, body)| (face.clone(), substitute(body, name, replacement)))
                .collect(),
        },

        Expr::Com {
            dimension,
            family,
            from,
            to,
            cap,
            tubes,
        } => Expr::Com {
            dimension: dimension.clone(),
            family: Box::new(substitute(family, name, replacement)),
            from: from.clone(),
            to: to.clone(),
            cap: Box::new(substitute(cap, name, replacement)),
            tubes: tubes
                .iter()
                .map(|(face, body)| (face.clone(), substitute(body, name, replacement)))
                .collect(),
        },

        Expr::PathP {
            dimension,
            family,
            left,
            right,
        } => Expr::PathP {
            dimension: dimension.clone(),
            family: Box::new(substitute(family, name, replacement)),
            left: Box::new(substitute(left, name, replacement)),
            right: Box::new(substitute(right, name, replacement)),
        },
        Expr::Coe {
            dimension,
            family,
            from,
            to,
            cap,
        } => Expr::Coe {
            dimension: dimension.clone(),
            family: Box::new(substitute(family, name, replacement)),
            from: from.clone(),
            to: to.clone(),
            cap: Box::new(substitute(cap, name, replacement)),
        },
        Expr::Name(current) if current == name => replacement.clone(),
        Expr::Equality { left, right } => Expr::Equality {
            left: Box::new(substitute(left, name, replacement)),
            right: Box::new(substitute(right, name, replacement)),
        },
        Expr::PathLambda { dimension, body } => Expr::PathLambda {
            dimension: dimension.clone(),
            body: Box::new(substitute(body, name, replacement)),
        },
        Expr::PathApply { path, dimension } => Expr::PathApply {
            path: Box::new(substitute(path, name, replacement)),
            dimension: dimension.clone(),
        },
        Expr::Pi {
            parameter,
            domain,
            codomain,
        } => Expr::Pi {
            parameter: parameter.clone(),
            domain: Box::new(substitute(domain, name, replacement)),
            codomain: if parameter.as_deref() == Some(name) {
                codomain.clone()
            } else {
                Box::new(substitute(codomain, name, replacement))
            },
        },
        Expr::Lambda { parameter, body } if parameter != name => Expr::Lambda {
            parameter: parameter.clone(),
            body: Box::new(substitute(body, name, replacement)),
        },
        Expr::Apply { function, argument } => Expr::Apply {
            function: Box::new(substitute(function, name, replacement)),
            argument: Box::new(substitute(argument, name, replacement)),
        },
        Expr::Let {
            name: binder,
            value,
            body,
        } => Expr::Let {
            name: binder.clone(),
            value: Box::new(substitute(value, name, replacement)),
            body: if binder == name {
                body.clone()
            } else {
                Box::new(substitute(body, name, replacement))
            },
        },
        Expr::Match {
            scrutinee,
            branches,
        } => Expr::Match {
            scrutinee: Box::new(substitute(scrutinee, name, replacement)),
            branches: branches
                .iter()
                .map(|branch| {
                    let shadows = pattern_binds(&branch.pattern, name);
                    super::ast::MatchBranch {
                        pattern: branch.pattern.clone(),
                        body: if shadows {
                            branch.body.clone()
                        } else {
                            substitute(&branch.body, name, replacement)
                        },
                    }
                })
                .collect(),
        },
        Expr::If {
            condition,
            then_branch,
            else_branch,
        } => Expr::If {
            condition: Box::new(substitute(condition, name, replacement)),
            then_branch: Box::new(substitute(then_branch, name, replacement)),
            else_branch: Box::new(substitute(else_branch, name, replacement)),
        },
        Expr::Suc(value) => Expr::Suc(Box::new(substitute(value, name, replacement))),
        _ => expr.clone(),
    }
}

fn replace_dim(dimension: &mut Dimension, old: &str, new: &Dimension) {
    if matches!(dimension, Dimension::Name(name) if name == old) {
        *dimension = new.clone();
    }
}

fn replace_face(face: &mut Face, old: &str, new: &Dimension) {
    match face {
        Face::Equal(a, b) => {
            replace_dim(a, old, new);
            replace_dim(b, old, new);
        }
        Face::And(a, b) | Face::Or(a, b) => {
            replace_face(a, old, new);
            replace_face(b, old, new);
        }
        Face::Top | Face::Bottom => {}
    }
}

#[cfg(test)]
mod pattern_tests {
    use super::*;
    use crate::surface::ast::{MatchBranch, Pattern};
    use crate::syntax::TelescopeEntry;

    #[test]
    fn higher_family_points_cannot_enter_ordinary_surface_resolution_or_matching() {
        let (mut core, id) = user_nat_core();
        let ids = core.inductives[id.index()]
            .constructors
            .ordinary()
            .unwrap()
            .iter()
            .copied()
            .map(crate::hit::ConstructorRef::Point)
            .collect();
        core.inductives[id.index()].constructors = crate::syntax::FamilyConstructors::Higher(ids);
        let elaborator = Elaborator {
            core,
            ..Elaborator::default()
        };
        assert!(
            elaborator
                .resolve_constructor("uzero")
                .unwrap_err()
                .message
                .contains("ordinary operation")
        );
        let branches = vec![MatchBranch {
            pattern: Pattern::Constructor {
                name: "uzero".into(),
                arguments: vec![],
            },
            body: Expr::Name("uzero".into()),
        }];
        assert!(elaborator.validate_constructor_branches(&branches).is_err());
    }

    fn user_nat_core() -> (Program, crate::syntax::InductiveId) {
        let mut core = Program::default();
        let nat = core.push_inductive("UserNat".to_owned(), 0, vec![], vec![]);
        core.push_constructor(nat, "uzero".to_owned(), vec![], vec![], vec![]);
        let pred_ty = core.alloc(Term::Inductive(nat), 0);
        core.push_constructor(
            nat,
            "usuc".to_owned(),
            vec![TelescopeEntry {
                name: "pred".to_owned(),
                ty: pred_ty,
            }],
            vec![],
            vec![0],
        );
        (core, nat)
    }

    fn recursive_nat_function(recursive_argument: &str) -> SurfaceProgram {
        SurfaceProgram {
            module: None,
            imports: vec![],
            declarations: vec![Item::Definition(Declaration {
                name: "f".to_owned(),
                ty: Some(Expr::Pi {
                    parameter: None,
                    domain: Box::new(Expr::Name("UserNat".to_owned())),
                    codomain: Box::new(Expr::Nat),
                }),
                value: Expr::Lambda {
                    parameter: "n".to_owned(),
                    body: Box::new(Expr::Match {
                        scrutinee: Box::new(Expr::Name("n".to_owned())),
                        branches: vec![
                            MatchBranch {
                                pattern: Pattern::Constructor {
                                    name: "uzero".to_owned(),
                                    arguments: vec![],
                                },
                                body: Expr::Zero,
                            },
                            MatchBranch {
                                pattern: Pattern::Constructor {
                                    name: "usuc".to_owned(),
                                    arguments: vec![Pattern::Name("pred".to_owned())],
                                },
                                body: Expr::Apply {
                                    function: Box::new(Expr::Name("f".to_owned())),
                                    argument: Box::new(Expr::Name(recursive_argument.to_owned())),
                                },
                            },
                        ],
                    }),
                },
            })],
        }
    }

    #[test]
    fn lowers_structural_recursive_call_to_induction_hypothesis() {
        let (core, _) = user_nat_core();
        let program = elaborate_into(core, &recursive_nat_function("pred")).unwrap();
        let Term::Lam(elim) = program.terms.get(program.decls[0].body).term else {
            panic!("expected function body");
        };
        let Term::Elim { methods, .. } = &program.terms.get(elim).term else {
            panic!("expected generic eliminator");
        };
        let Term::Lam(inner) = program.terms.get(methods[1]).term else {
            panic!("expected constructor argument binder");
        };
        let Term::Lam(body) = program.terms.get(inner).term else {
            panic!("expected induction hypothesis binder");
        };
        assert!(matches!(program.terms.get(body).term, Term::Var(0)));
    }

    #[test]
    fn rejects_non_structural_recursive_call() {
        let (core, _) = user_nat_core();
        let error = elaborate_into(core, &recursive_nat_function("n")).unwrap_err();
        assert!(
            error
                .message
                .contains("recursive call is not on a structurally smaller argument")
        );
    }

    #[test]
    fn parses_and_lowers_structural_recursion_end_to_end() {
        let (core, _) = user_nat_core();
        let surface = crate::surface::parser::parse(
            "def f (n : UserNat) : Nat = match n { uzero => zero; usuc pred => f pred }",
        )
        .unwrap();
        let program = elaborate_into(core, &surface).unwrap();

        let Term::Lam(elim) = program.terms.get(program.decls[0].body).term else {
            panic!("expected function body");
        };
        let Term::Elim { methods, .. } = &program.terms.get(elim).term else {
            panic!("expected generic eliminator");
        };
        let Term::Lam(inner) = program.terms.get(methods[1]).term else {
            panic!("expected constructor argument binder");
        };
        let Term::Lam(body) = program.terms.get(inner).term else {
            panic!("expected induction hypothesis binder");
        };
        assert!(matches!(program.terms.get(body).term, Term::Var(0)));
    }

    #[test]
    fn lowers_indexed_vec_match_with_parameters_indices_and_tail_ih() {
        let mut core = Program::default();
        let type0 = core.alloc(Term::U(0), 0);
        let nat_ty = core.alloc(Term::Nat, 0);
        let vec = core.push_inductive(
            "Vec".to_owned(),
            0,
            vec![TelescopeEntry {
                name: "A".to_owned(),
                ty: type0,
            }],
            vec![TelescopeEntry {
                name: "length".to_owned(),
                ty: nat_ty,
            }],
        );
        let zero = core.alloc(Term::Zero, 0);
        core.push_constructor(vec, "nil".to_owned(), vec![], vec![zero], vec![]);
        let n_ty = core.alloc(Term::Nat, 0);
        let a_var = core.alloc(Term::Var(1), 0);
        let vec_head = core.alloc(Term::Inductive(vec), 0);
        let tail_a = core.alloc(Term::Var(2), 0);
        let vec_a = core.alloc(Term::App(vec_head, tail_a), 0);
        let tail_n = core.alloc(Term::Var(1), 0);
        let vec_a_n = core.alloc(Term::App(vec_a, tail_n), 0);
        let result_n = core.alloc(Term::Var(2), 0);
        let suc_n = core.alloc(Term::Suc(result_n), 0);
        core.push_constructor(
            vec,
            "cons".to_owned(),
            vec![
                TelescopeEntry {
                    name: "n".to_owned(),
                    ty: n_ty,
                },
                TelescopeEntry {
                    name: "head".to_owned(),
                    ty: a_var,
                },
                TelescopeEntry {
                    name: "tail".to_owned(),
                    ty: vec_a_n,
                },
            ],
            vec![suc_n],
            vec![2],
        );

        let vec_a = Expr::Apply {
            function: Box::new(Expr::Name("Vec".to_owned())),
            argument: Box::new(Expr::Name("A".to_owned())),
        };
        let vec_a_n = Expr::Apply {
            function: Box::new(vec_a),
            argument: Box::new(Expr::Name("n".to_owned())),
        };
        let surface = SurfaceProgram {
            module: None,
            imports: vec![],
            declarations: vec![Item::Definition(Declaration {
                name: "length".to_owned(),
                ty: Some(Expr::Pi {
                    parameter: Some("A".to_owned()),
                    domain: Box::new(Expr::Universe(0)),
                    codomain: Box::new(Expr::Pi {
                        parameter: Some("n".to_owned()),
                        domain: Box::new(Expr::Nat),
                        codomain: Box::new(Expr::Pi {
                            parameter: None,
                            domain: Box::new(vec_a_n),
                            codomain: Box::new(Expr::Nat),
                        }),
                    }),
                }),
                value: Expr::Lambda {
                    parameter: "A".to_owned(),
                    body: Box::new(Expr::Lambda {
                        parameter: "n".to_owned(),
                        body: Box::new(Expr::Lambda {
                            parameter: "xs".to_owned(),
                            body: Box::new(Expr::Match {
                                scrutinee: Box::new(Expr::Name("xs".to_owned())),
                                branches: vec![
                                    MatchBranch {
                                        pattern: Pattern::Constructor {
                                            name: "nil".to_owned(),
                                            arguments: vec![],
                                        },
                                        body: Expr::Zero,
                                    },
                                    MatchBranch {
                                        pattern: Pattern::Constructor {
                                            name: "cons".to_owned(),
                                            arguments: vec![
                                                Pattern::Name("m".to_owned()),
                                                Pattern::Name("head".to_owned()),
                                                Pattern::Name("tail".to_owned()),
                                            ],
                                        },
                                        body: Expr::Suc(Box::new(Expr::Apply {
                                            function: Box::new(Expr::Apply {
                                                function: Box::new(Expr::Apply {
                                                    function: Box::new(Expr::Name(
                                                        "length".to_owned(),
                                                    )),
                                                    argument: Box::new(Expr::Name("A".to_owned())),
                                                }),
                                                argument: Box::new(Expr::Name("m".to_owned())),
                                            }),
                                            argument: Box::new(Expr::Name("tail".to_owned())),
                                        })),
                                    },
                                ],
                            }),
                        }),
                    }),
                },
            })],
        };

        let program = elaborate_into(core, &surface).unwrap();
        let mut term = program.decls[0].body;
        for _ in 0..3 {
            let Term::Lam(body) = program.terms.get(term).term else {
                panic!("expected function binder");
            };
            term = body;
        }
        let Term::Elim {
            inductive,
            parameters,
            indices,
            methods,
            ..
        } = &program.terms.get(term).term
        else {
            panic!("expected generic eliminator");
        };
        assert_eq!(*inductive, vec);
        assert_eq!(parameters.len(), 1);
        assert_eq!(indices.len(), 1);
        assert_eq!(methods.len(), 2);
    }

    #[test]
    fn rejects_structural_recursion_with_wrong_prefix() {
        let mut elaborator = Elaborator {
            current_definition: Some("length".to_owned()),
            ..Elaborator::default()
        };
        elaborator.locals.push(("A".to_owned(), Expr::Universe(0)));
        elaborator.locals.push(("n".to_owned(), Expr::Nat));
        elaborator.locals.push(("m".to_owned(), Expr::Nat));
        elaborator
            .locals
            .push(("tail".to_owned(), Expr::Name("VecTail".to_owned())));
        elaborator.locals.push(("<ih:tail>".to_owned(), Expr::Nat));
        elaborator.recursive_calls.insert(
            "tail".to_owned(),
            (
                "<ih:tail>".to_owned(),
                vec![Expr::Name("A".to_owned()), Expr::Name("m".to_owned())],
            ),
        );

        let call = |parameter: Expr, index: Expr| Expr::Apply {
            function: Box::new(Expr::Apply {
                function: Box::new(Expr::Apply {
                    function: Box::new(Expr::Name("length".to_owned())),
                    argument: Box::new(parameter),
                }),
                argument: Box::new(index),
            }),
            argument: Box::new(Expr::Name("tail".to_owned())),
        };

        let wrong_parameter = elaborator
            .term(&call(Expr::Bool, Expr::Name("m".to_owned())))
            .unwrap_err();
        assert!(
            wrong_parameter
                .message
                .contains("parameters or indices do not match")
        );

        let wrong_index = elaborator
            .term(&call(
                Expr::Name("A".to_owned()),
                Expr::Name("n".to_owned()),
            ))
            .unwrap_err();
        assert!(
            wrong_index
                .message
                .contains("parameters or indices do not match")
        );
    }

    #[test]
    fn resolves_constructor_patterns_from_core_metadata() {
        let mut core = Program::default();
        let nat = core.push_inductive("UserNat".to_owned(), 0, vec![], vec![]);
        let zero = core.push_constructor(nat, "uzero".to_owned(), vec![], vec![], vec![]);
        let pred_ty = core.alloc(Term::Inductive(nat), 0);
        let pred = TelescopeEntry {
            name: "pred".to_owned(),
            ty: pred_ty,
        };
        core.push_constructor(nat, "usuc".to_owned(), vec![pred], vec![], vec![0]);

        let elaborator = Elaborator {
            core,
            ..Elaborator::default()
        };
        assert_eq!(elaborator.resolve_constructor("uzero").unwrap(), zero);
        assert!(elaborator.resolve_constructor("missing").is_err());
    }

    #[test]
    fn rejects_ambiguous_constructor_names() {
        let mut core = Program::default();
        let left = core.push_inductive("Left".to_owned(), 0, vec![], vec![]);
        let right = core.push_inductive("Right".to_owned(), 0, vec![], vec![]);
        core.push_constructor(left, "same".to_owned(), vec![], vec![], vec![]);
        core.push_constructor(right, "same".to_owned(), vec![], vec![], vec![]);

        let elaborator = Elaborator {
            core,
            ..Elaborator::default()
        };
        let error = elaborator.resolve_constructor("same").unwrap_err();
        assert!(error.message.contains("ambiguous constructor"));
    }

    #[test]
    fn lowers_non_dependent_surface_match_to_eliminator() {
        let mut core = Program::default();
        let nat = core.push_inductive("UserNat".to_owned(), 0, vec![], vec![]);
        core.push_constructor(nat, "uzero".to_owned(), vec![], vec![], vec![]);
        let pred_ty = core.alloc(Term::Inductive(nat), 0);
        core.push_constructor(
            nat,
            "usuc".to_owned(),
            vec![TelescopeEntry {
                name: "pred".to_owned(),
                ty: pred_ty,
            }],
            vec![],
            vec![0],
        );
        let surface = SurfaceProgram {
            module: None,
            imports: vec![],
            declarations: vec![Item::Definition(Declaration {
                name: "f".to_owned(),
                ty: Some(Expr::Pi {
                    parameter: None,
                    domain: Box::new(Expr::Name("UserNat".to_owned())),
                    codomain: Box::new(Expr::Nat),
                }),
                value: Expr::Lambda {
                    parameter: "n".to_owned(),
                    body: Box::new(Expr::Match {
                        scrutinee: Box::new(Expr::Name("n".to_owned())),
                        branches: vec![
                            MatchBranch {
                                pattern: Pattern::Constructor {
                                    name: "uzero".to_owned(),
                                    arguments: vec![],
                                },
                                body: Expr::Zero,
                            },
                            MatchBranch {
                                pattern: Pattern::Constructor {
                                    name: "usuc".to_owned(),
                                    arguments: vec![Pattern::Name("pred".to_owned())],
                                },
                                body: Expr::Zero,
                            },
                        ],
                    }),
                },
            })],
        };
        let program = elaborate_into(core, &surface).unwrap();
        let body = program.decls[0].body;
        let Term::Lam(match_term) = program.terms.get(body).term else {
            panic!("expected function body");
        };
        let Term::Elim {
            inductive,
            parameters,
            methods,
            indices,
            ..
        } = &program.terms.get(match_term).term
        else {
            panic!("expected generic eliminator");
        };
        assert_eq!(*inductive, nat);
        assert!(parameters.is_empty());
        assert!(indices.is_empty());
        assert_eq!(methods.len(), 2);
    }
}
