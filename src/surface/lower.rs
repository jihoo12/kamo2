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
        emit(ty, &mut out)?;
        out.push(' ');
        emit(&declaration.value, &mut out)?;
        out.push_str(")\n");
    }
    Ok(out)
}

fn emit(expr: &Expr, out: &mut String) -> Result<()> {
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
        Expr::Suc(value) => unary("suc", value, out)?,
        Expr::Pi {
            parameter,
            domain,
            codomain,
        } => {
            out.push_str("(Pi ");
            out.push_str(parameter.as_deref().unwrap_or("_"));
            out.push(' ');
            emit(domain, out)?;
            out.push(' ');
            emit(codomain, out)?;
            out.push(')');
        }
        Expr::Lambda { parameter, body } => {
            out.push_str("(lam ");
            out.push_str(parameter);
            out.push(' ');
            emit(body, out)?;
            out.push(')');
        }
        Expr::Apply { function, argument } => {
            out.push_str("(app ");
            emit(function, out)?;
            out.push(' ');
            emit(argument, out)?;
            out.push(')');
        }
        Expr::Let { name, value, body } => {
            // The core cannot infer a bare lambda in function position, so annotate
            // the lambda with the Pi type obtained from the let-bound value.
            let value_ty = simple_type(value).ok_or_else(|| {
                Error::plain("cannot infer let-bound value type; add surface let annotations later")
            })?;
            out.push_str("(app (ann (lam ");
            out.push_str(name);
            out.push(' ');
            emit(body, out)?;
            out.push_str(") (Pi _ ");
            emit(&value_ty, out)?;
            out.push(' ');
            // The codomain is only needed to infer the lambda application. For the
            // initial surface milestone, infer it from the body when it is simple.
            let body_ty = simple_type(body).ok_or_else(|| {
                Error::plain("cannot infer let body type; add surface let annotations later")
            })?;
            emit(&body_ty, out)?;
            out.push_str(")) ");
            emit(value, out)?;
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
            emit(condition, out)?;
            out.push(' ');
            emit(then_branch, out)?;
            out.push(' ');
            emit(else_branch, out)?;
            out.push(')');
        }
    }
    Ok(())
}

fn simple_type(expr: &Expr) -> Option<Expr> {
    match expr {
        Expr::True | Expr::False => Some(Expr::Bool),
        Expr::Zero | Expr::Suc(_) => Some(Expr::Nat),
        Expr::Bool | Expr::Nat => Some(Expr::Universe(0)),
        Expr::Universe(level) => level.checked_add(1).map(Expr::Universe),
        _ => None,
    }
}

fn unary(name: &str, value: &Expr, out: &mut String) {
    out.push('(');
    out.push_str(name);
    out.push(' ');
    emit(value, out)?;
    out.push(')');
}
