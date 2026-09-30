use super::ast::{Declaration, Expr, Program as SurfaceProgram};
use crate::syntax::{Program, Term, TermId};
use crate::{Error, Result};
use std::collections::HashMap;

pub(crate) fn elaborate(surface: &SurfaceProgram) -> Result<Program> {
    Elaborator::default().program(surface)
}

#[derive(Default)]
struct Elaborator {
    core: Program,
    globals: HashMap<String, usize>,
    global_types: HashMap<String, Expr>,
    locals: Vec<(String, Expr)>,
}

impl Elaborator {
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
        let body = self.term_expected(&declaration.value, Some(ty_expr))?;
        let index = self.core.decls.len();
        self.core.push_decl(declaration.name.clone(), ty, body);
        self.globals.insert(declaration.name.clone(), index);
        self.global_types
            .insert(declaration.name.clone(), ty_expr.clone());
        Ok(())
    }

    fn term(&mut self, expr: &Expr) -> Result<TermId> {
        self.term_expected(expr, None)
    }

    fn term_expected(&mut self, expr: &Expr, expected: Option<&Expr>) -> Result<TermId> {
        let term = match expr {
            Expr::Name(name) => {
                if let Some(index) = self.locals.iter().rev().position(|(local, _)| local == name) {
                    Term::Var(index)
                } else if let Some(index) = self.globals.get(name) {
                    Term::Global(*index)
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
                let function_ty = self.infer(function).ok();
                let function = self.term(function)?;
                let argument = match function_ty.as_ref() {
                    Some(Expr::Pi { domain, .. }) => self.term_expected(argument, Some(domain))?,
                    _ => self.term(argument)?,
                };
                Term::App(function, argument)
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
        };
        Ok(self.core.alloc(term, 0))
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
                .ok_or_else(|| Error::plain(format!("cannot infer type of '{name}'"))),
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
                _ => Err(Error::plain("cannot apply a non-function surface expression")),
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
                };
                let codomain_level = universe_level(&nested.infer(codomain)?)?;
                Ok(Expr::Universe(domain_level.max(codomain_level)))
            }
            Expr::Lambda { .. } => Err(Error::plain(
                "cannot infer an unannotated lambda in a let binding",
            )),
            Expr::If { .. } => Err(Error::plain("cannot infer surface if yet")),
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
