//! Abstract syntax for Kamo2's functional surface language.

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program {
    pub declarations: Vec<Declaration>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Declaration {
    pub name: String,
    pub ty: Option<Expr>,
    pub value: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    Name(String),
    Universe(u32),
    Bool,
    True,
    False,
    Nat,
    Zero,
    Suc(Box<Expr>),
    Pi {
        parameter: Option<String>,
        domain: Box<Expr>,
        codomain: Box<Expr>,
    },
    Lambda {
        parameter: String,
        body: Box<Expr>,
    },
    Apply {
        function: Box<Expr>,
        argument: Box<Expr>,
    },
    Let {
        name: String,
        value: Box<Expr>,
        body: Box<Expr>,
    },
    If {
        condition: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Box<Expr>,
    },
}
