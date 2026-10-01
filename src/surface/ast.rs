//! Abstract syntax for Kamo2's functional surface language.

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program {
    pub module: Option<String>,
    pub imports: Vec<String>,
    pub declarations: Vec<Item>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Item {
    Definition(Declaration),
    Data(DataDeclaration),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DataDeclaration {
    pub name: String,
    pub parameters: Vec<(String, Expr)>,
    pub indices: Vec<(String, Expr)>,
    pub universe: u32,
    pub constructors: Vec<ConstructorDeclaration>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstructorDeclaration {
    pub name: String,
    /// Constructor arguments only; the parser verifies and removes the result.
    pub arguments: Vec<(String, Expr)>,
    pub result: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Declaration {
    pub name: String,
    pub ty: Option<Expr>,
    pub value: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatchBranch {
    pub pattern: Pattern,
    pub body: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern {
    Name(String),
    Constructor {
        name: String,
        arguments: Vec<Pattern>,
    },
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
    Match {
        scrutinee: Box<Expr>,
        branches: Vec<MatchBranch>,
    },
}
