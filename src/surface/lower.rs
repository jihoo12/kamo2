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
        emit(ty, &mut out);
        out.push(' ');
        emit(&declaration.value, &mut out);
        out.push_str(")\n");
    }
    Ok(out)
}

fn emit(expr: &Expr, out: &mut String) {
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
        Expr::Suc(value) => unary("suc", value, out),
        Expr::Pi {
            parameter,
            domain,
            codomain,
        } => {
            out.push_str("(Pi ");
            out.push_str(parameter.as_deref().unwrap_or("_"));
            out.push(' ');
            emit(domain, out);
            out.push(' ');
            emit(codomain, out);
            out.push(')');
        }
        Expr::Lambda { parameter, body } => {
            out.push_str("(lam ");
            out.push_str(parameter);
            out.push(' ');
            emit(body, out);
            out.push(')');
        }
        Expr::Apply { function, argument } => {
            out.push_str("(app ");
            emit(function, out);
            out.push(' ');
            emit(argument, out);
            out.push(')');
        }
        Expr::Let { name, value, body } => {
            // The core has no let primitive: (let x = v; b) elaborates to (\x => b) v.
            out.push_str("(app (lam ");
            out.push_str(name);
            out.push(' ');
            emit(body, out);
            out.push_str(") ");
            emit(value, out);
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
            emit(condition, out);
            out.push(' ');
            emit(then_branch, out);
            out.push(' ');
            emit(else_branch, out);
            out.push(')');
        }
    }
}

fn unary(name: &str, value: &Expr, out: &mut String) {
    out.push('(');
    out.push_str(name);
    out.push(' ');
    emit(value, out);
    out.push(')');
}
