use super::ast::{Declaration, Expr, Pattern, Program as SurfaceProgram};
use crate::arena::Key;
use crate::syntax::{ConstructorId, Program, Term, TermId};
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

    fn resolve_constructor(&self, name: &str) -> Result<ConstructorId> {
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
        for declaration in &surface.declarations {
            self.declaration(declaration)?;
        }
        Ok(self.core)
    }

    fn declaration(&mut self, declaration: &Declaration) -> Result<()> {
        if self.globals.contains_key(&declaration.name)
            || ["Bool", "Nat", "true", "false", "zero"].contains(&declaration.name.as_str())
        {
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

    fn lower_match(
        &mut self,
        scrutinee: &Expr,
        branches: &[super::ast::MatchBranch],
        expected: &Expr,
    ) -> Result<TermId> {
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

        let motive_body = self.term(expected)?;
        let motive = self.lambda_n(motive_body, declaration.indices.len() + 1);

        let mut methods = Vec::with_capacity(declaration.constructors.len());
        for constructor_id in &declaration.constructors {
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

            let mut pushed = 0;
            let mut metadata_names = parameter_exprs
                .iter()
                .map(|parameter| match parameter {
                    Expr::Name(name) => name.clone(),
                    _ => "<parameter>".to_owned(),
                })
                .collect::<Vec<_>>();
            for (argument_index, (argument, entry)) in
                arguments.iter().zip(&constructor.arguments).enumerate()
            {
                let Pattern::Name(name) = argument else {
                    return Err(Error::plain(
                        "nested constructor patterns are not supported yet",
                    ));
                };
                let ty = self.surface_type_in(entry.ty, &metadata_names)?;
                self.locals.push((name.clone(), ty.clone()));
                metadata_names.push(name.clone());
                pushed += 1;
                if constructor.recursive_arguments.contains(&argument_index) {
                    let (recursive_family, mut recursive_parameters, recursive_indices) =
                        self.inductive_application(&ty)?;
                    if recursive_family != inductive {
                        return Err(Error::plain(
                            "recursive constructor argument belongs to the wrong family",
                        ));
                    }
                    recursive_parameters.extend(recursive_indices);
                    let ih = format!("<ih:{}>", name);
                    self.locals.push((ih.clone(), expected.clone()));
                    self.recursive_calls
                        .insert(name.clone(), (ih, recursive_parameters));
                    pushed += 1;
                }
            }
            let body = self.term_expected(&branch.body, Some(expected));
            for argument in arguments {
                if let Pattern::Name(name) = argument {
                    self.recursive_calls.remove(name);
                }
            }
            for _ in 0..pushed {
                self.locals.pop();
            }
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

    fn term(&mut self, expr: &Expr) -> Result<TermId> {
        self.term_expected(expr, None)
    }

    fn term_expected(&mut self, expr: &Expr, expected: Option<&Expr>) -> Result<TermId> {
        let term = match expr {
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
                } else if let Ok(constructor) = self.resolve_constructor(name) {
                    Term::Constructor(constructor)
                } else {
                    return Err(Error::plain(format!("unknown name '{name}'")));
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
                let mut head = expr;
                let mut recursive_arguments = Vec::new();
                while let Expr::Apply { function, argument } = head {
                    recursive_arguments.push(&**argument);
                    head = function;
                }
                recursive_arguments.reverse();

                if let Expr::Name(function_name) = head
                    && self.current_definition.as_ref() == Some(function_name)
                {
                    let Some(Expr::Name(argument_name)) = recursive_arguments.last() else {
                        return Err(Error::plain(
                            "recursive calls must target a structural argument",
                        ));
                    };
                    let (ih, expected_prefix) =
                        self.recursive_calls.get(argument_name).ok_or_else(|| {
                            Error::plain("recursive call is not on a structurally smaller argument")
                        })?;
                    let actual_prefix =
                        &recursive_arguments[..recursive_arguments.len().saturating_sub(1)];
                    if actual_prefix.len() != expected_prefix.len()
                        || actual_prefix
                            .iter()
                            .zip(expected_prefix)
                            .any(|(actual, expected)| *actual != expected)
                    {
                        return Err(Error::plain(
                            "recursive call parameters or indices do not match the recursive argument",
                        ));
                    }
                    let index = self
                        .locals
                        .iter()
                        .rev()
                        .position(|(local, _)| local == ih)
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
                return self.lower_match(scrutinee, branches, expected);
            }
        };
        Ok(self.core.alloc(term, 0))
    }

    fn infer_metadata_name(&self, name: &str) -> Result<Expr> {
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
        Err(Error::plain(format!("cannot infer type of '{name}'")))
    }

    fn surface_type_in(&self, term: TermId, names: &[String]) -> Result<Expr> {
        match self.core.terms.get(term).term.clone() {
            Term::U(level) => Ok(Expr::Universe(level)),
            Term::Bool => Ok(Expr::Bool),
            Term::Nat => Ok(Expr::Nat),
            Term::Inductive(inductive) => Ok(Expr::Name(
                self.core.inductives[inductive.index()].name.clone(),
            )),
            Term::App(function, argument) => Ok(Expr::Apply {
                function: Box::new(self.surface_type_in(function, names)?),
                argument: Box::new(self.surface_type_in(argument, names)?),
            }),
            Term::Var(index) => names
                .iter()
                .rev()
                .nth(index)
                .map(|name| Expr::Name(name.clone()))
                .ok_or_else(|| Error::plain("inductive metadata contains an escaped variable")),
            _ => Err(Error::plain(
                "inductive metadata type is not representable in surface syntax",
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

    fn infer(&self, expr: &Expr) -> Result<Expr> {
        match expr {
            Expr::Name(name) => self
                .locals
                .iter()
                .rev()
                .find(|(local, _)| local == name)
                .map(|(_, ty)| ty.clone())
                .or_else(|| self.global_types.get(name).cloned())
                .map(Ok)
                .unwrap_or_else(|| self.infer_metadata_name(name)),
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
                let mut locals = self.locals.clone();
                locals.push((name.clone(), value_ty));
                let nested = Elaborator {
                    core: Program::default(),
                    globals: self.globals.clone(),
                    global_types: self.global_types.clone(),
                    locals,
                    current_definition: self.current_definition.clone(),
                    recursive_calls: self.recursive_calls.clone(),
                };
                nested.infer(body)
            }
            Expr::Pi {
                parameter,
                domain,
                codomain,
            } => {
                let domain_level = universe_level(&self.infer(domain)?)?;
                let mut locals = self.locals.clone();
                locals.push((
                    parameter.clone().unwrap_or_else(|| "_".to_owned()),
                    (**domain).clone(),
                ));
                let nested = Elaborator {
                    core: Program::default(),
                    globals: self.globals.clone(),
                    global_types: self.global_types.clone(),
                    locals,
                    current_definition: self.current_definition.clone(),
                    recursive_calls: self.recursive_calls.clone(),
                };
                let codomain_level = universe_level(&nested.infer(codomain)?)?;
                Ok(Expr::Universe(domain_level.max(codomain_level)))
            }
            Expr::Lambda { .. } => Err(Error::plain(
                "cannot infer an unannotated lambda in a let binding",
            )),
            Expr::If { .. } => Err(Error::plain("cannot infer surface if yet")),
            Expr::Match { .. } => Err(Error::plain("cannot infer surface match yet")),
        }
    }
}

fn universe_level(expr: &Expr) -> Result<u32> {
    if let Expr::Universe(level) = expr {
        Ok(*level)
    } else {
        Err(Error::plain("expected a surface type"))
    }
}

fn substitute(expr: &Expr, name: &str, replacement: &Expr) -> Expr {
    match expr {
        Expr::Name(current) if current == name => replacement.clone(),
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
        Expr::Suc(value) => Expr::Suc(Box::new(substitute(value, name, replacement))),
        _ => expr.clone(),
    }
}

#[cfg(test)]
mod pattern_tests {
    use super::*;
    use crate::surface::ast::{MatchBranch, Pattern};
    use crate::syntax::TelescopeEntry;

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
            declarations: vec![Declaration {
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
            }],
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
            declarations: vec![Declaration {
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
            }],
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
        elaborator.locals.push(("tail".to_owned(), Expr::Name("VecTail".to_owned())));
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
            declarations: vec![Declaration {
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
            }],
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
