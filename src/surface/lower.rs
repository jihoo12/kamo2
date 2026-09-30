use super::ast::{Expr, Program};
use crate::{Error, Result};

pub(crate) fn to_core_source(program: &Program) -> Result<String> {
    let mut out = String::new();
    for declaration in &program.declarations {
        let ty = declaration
            .ty
            .as_ref()
            .ok_or_else(|| Error::plain("surface definitions require a type annotation"))?;
        out.push_str("(def ");
        out.push_str(&declaration.name);
        out.push(' ');
        emit(ty, &mut out, &[])?;
        out.push(' ');
        emit(&declaration.value, &mut out, &[])?;
        out.push_str(")\n");
    }
    Ok(out)
}

fn emit(expr: &Expr, out: &mut String, locals: &[(String, Expr)]) -> Result<()> {
    match expr {
        Expr::Name(name) => out.push_str(name),
        Expr::Universe(level) => {
            out.push_str("(U ");
            out.push_str(&level.to_string());
            out.push(')');
        }
        Expr::Bool => out.push_str("Bool"),
        Expr::True => out.push_str("true"),
        Expr::False => out.push_str("false"),
        Expr::Nat => out.push_str("Nat"),
        Expr::Zero => out.push_str("zero"),
        Expr::Suc(value) => unary("suc", value, out, locals)?,
        Expr::Pi {
            parameter,
            domain,
            codomain,
        } => {
            out.push_str("(Pi ");
            out.push_str(parameter.as_deref().unwrap_or("_"));
            out.push(' ');
            emit(domain, out, locals)?;
            out.push(' ');
            emit(codomain, out, locals)?;
            out.push(')');
        }
        Expr::Lambda { parameter, body } => {
            out.push_str("(lam ");
            out.push_str(parameter);
            out.push(' ');
            emit(body, out, locals)?;
            out.push(')');
        }
        Expr::Apply { function, argument } => {
            out.push_str("(app ");
            emit(function, out, locals)?;
            out.push(' ');
            emit(argument, out, locals)?;
            out.push(')');
        }
        Expr::Let { name, value, body } => {
            // The core cannot infer a bare lambda in function position, so annotate
            // the lambda with the Pi type obtained from the let-bound value.
            let value_ty = simple_type(value, locals).ok_or_else(|| {
                Error::plain("cannot infer let-bound value type; add surface let annotations later")
            })?;
            let mut body_locals = locals.to_vec();
            body_locals.push((name.clone(), value_ty.clone()));
            let body_ty = simple_type(body, &body_locals).ok_or_else(|| {
                Error::plain("cannot infer let body type; add surface let annotations later")
            })?;
            out.push_str("(app (ann (lam ");
            out.push_str(name);
            out.push(' ');
            emit(body, out, &body_locals)?;
            out.push_str(") (Pi _ ");
            emit(&value_ty, out, locals)?;
            out.push(' ');
            emit(&body_ty, out, &body_locals)?;
            out.push_str(")) ");
            emit(value, out, locals)?;
            out.push(')');
        }
        Expr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            // Bool elimination needs a motive. This surface node is reserved until
            // motive synthesis is part of elaboration.
            out.push_str("(surface-if ");
            emit(condition, out, locals)?;
            out.push(' ');
            emit(then_branch, out, locals)?;
            out.push(' ');
            emit(else_branch, out, locals)?;
            out.push(')');
        }
    }
    Ok(())
}

fn simple_type(expr: &Expr, locals: &[(String, Expr)]) -> Option<Expr> {
    match expr {
        Expr::Name(name) => locals
            .iter()
            .rev()
            .find(|(local, _)| local == name)
            .map(|(_, ty)| ty.clone()),
        Expr::True | Expr::False => Some(Expr::Bool),
        Expr::Zero | Expr::Suc(_) => Some(Expr::Nat),
        Expr::Bool | Expr::Nat => Some(Expr::Universe(0)),
        Expr::Universe(level) => level.checked_add(1).map(Expr::Universe),
        _ => None,
    }
}

fn unary(name: &str, value: &Expr, out: &mut String, locals: &[(String, Expr)]) -> Result<()> {
    out.push('(');
    out.push_str(name);
    out.push(' ');
    emit(value, out, locals)?;
    out.push(')');
    Ok(())
}
