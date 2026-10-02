use crate::arena::{Arena, Key, key};
use crate::hit::{ConstructorRef, HigherConstructorDecl, HigherConstructorId};
use crate::{Error, Result};
use std::collections::HashMap;
key!(TermId);
key!(InductiveId);
key!(ConstructorId);

#[derive(Clone, Copy, Debug)]
pub(crate) enum D {
    Zero,
    One,
    Bound(usize),
}
#[derive(Clone, Debug)]
pub(crate) enum F {
    Top,
    Bot,
    Eq(D, D),
    And(Box<F>, Box<F>),
    Or(Box<F>, Box<F>),
}
#[derive(Clone, Debug)]
pub(crate) enum Term {
    Var(usize),
    Global(usize),
    U(u32),
    Pi(TermId, TermId),
    Sigma(TermId, TermId),
    Lam(TermId),
    App(TermId, TermId),
    Pair(TermId, TermId),
    Fst(TermId),
    Snd(TermId),
    Bool,
    True,
    False,
    If(TermId, TermId, TermId, TermId),
    Nat,
    #[allow(dead_code)]
    Inductive(InductiveId),
    #[allow(dead_code)]
    Constructor(ConstructorId),
    #[allow(dead_code)] // Constructed through the internal Slice C API, not the parser.
    HigherApp {
        constructor: HigherConstructorId,
        parameters: Vec<TermId>,
        arguments: Vec<TermId>,
        dimensions: Vec<D>,
    },
    #[allow(dead_code)]
    Elim {
        inductive: InductiveId,
        parameters: Vec<TermId>,
        motive: TermId,
        methods: Vec<TermId>,
        indices: Vec<TermId>,
        scrutinee: TermId,
    },
    Zero,
    Suc(TermId),
    NatElim(TermId, TermId, TermId, TermId),
    Ann(TermId, TermId),
    Path(TermId, TermId, TermId),
    PLam(TermId),
    PApp(TermId, D),
    Com {
        family: TermId,
        from: D,
        to: D,
        cap: TermId,
        tubes: Vec<(F, TermId)>,
    },
    System(TermId, Vec<(F, TermId)>),
    Glue(TermId, Vec<(F, TermId, TermId)>),
    GlueIntro(TermId, TermId, Vec<(F, TermId)>),
    Unglue(TermId, TermId),
}
#[derive(Clone, Debug)]
pub(crate) struct Node {
    pub term: Term,
    pub offset: usize,
}
#[derive(Clone, Debug)]
pub(crate) struct Decl {
    pub name: String,
    pub ty: TermId,
    pub body: TermId,
}

#[allow(dead_code)]
#[derive(Clone, Debug)]
pub(crate) struct TelescopeEntry {
    pub name: String,
    pub ty: TermId,
}

pub(crate) type Telescope = Vec<TelescopeEntry>;

#[allow(dead_code)]
#[derive(Clone, Debug)]
pub(crate) struct ConstructorDecl {
    pub id: ConstructorId,
    pub inductive: InductiveId,
    pub name: String,
    pub arguments: Telescope,
    pub result_indices: Vec<TermId>,
    pub recursive_arguments: Vec<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug)]
pub(crate) struct InductiveDecl {
    pub id: InductiveId,
    pub name: String,
    pub universe: u32,
    pub parameters: Telescope,
    pub indices: Telescope,
    pub constructors: FamilyConstructors,
}
#[derive(Clone, Debug)]
pub(crate) enum FamilyConstructors {
    Ordinary(Vec<ConstructorId>),
    Higher(Vec<ConstructorRef>),
}
impl FamilyConstructors {
    pub(crate) fn ordinary(&self) -> Result<&[ConstructorId]> {
        match self {
            Self::Ordinary(ids) => Ok(ids),
            Self::Higher(_) => Err(Error::plain(
                "ordinary operation on Higher family is forbidden",
            )),
        }
    }
    pub(crate) fn is_higher(&self) -> bool {
        matches!(self, Self::Higher(_))
    }
}
#[derive(Default, Debug)]
pub(crate) struct Program {
    pub terms: Arena<TermId, Node>,
    pub decls: Vec<Decl>,
    #[allow(dead_code)]
    pub inductives: Vec<InductiveDecl>,
    #[allow(dead_code)]
    pub constructors: Vec<ConstructorDecl>,
    pub higher: Vec<HigherConstructorDecl>,
}

impl Program {
    /// Validate the trusted, resolved representation of ordinary inductives.
    /// This deliberately accepts only direct recursive arguments. Any nested
    /// occurrence (including an occurrence in a function domain) is rejected.
    pub(crate) fn validate_inductives(&self) -> Result<()> {
        if !self.higher.is_empty()
            || self.inductives.iter().any(|f| f.constructors.is_higher())
            || (0..self.terms.len())
                .any(|i| matches!(self.terms.get(TermId::new(i)).term, Term::HigherApp { .. }))
        {
            return crate::hit::validate_executable(self);
        }
        for (position, family) in self.inductives.iter().enumerate() {
            if family.id.index() != position {
                return Err(Error::plain("malformed inductive id"));
            }
            let mut bound = 0;
            for entry in &family.parameters {
                self.validate_scoped(entry.ty, bound, 0)?;
                if self.contains_inductive(entry.ty, family.id, 0)? {
                    return Err(Error::plain(
                        "inductive family occurs in its own parameter telescope",
                    ));
                }
                bound += 1;
            }
            for entry in &family.indices {
                self.validate_scoped(entry.ty, bound, 0)?;
                if self.contains_inductive(entry.ty, family.id, 0)? {
                    return Err(Error::plain(
                        "inductive family occurs in its own index telescope",
                    ));
                }
                bound += 1;
            }
            for constructor_id in family.constructors.ordinary()? {
                let constructor = self
                    .constructors
                    .get(constructor_id.index())
                    .ok_or_else(|| Error::plain("inductive references a missing constructor"))?;
                if constructor.id != *constructor_id || constructor.inductive != family.id {
                    return Err(Error::plain(
                        "constructor ownership metadata is inconsistent",
                    ));
                }
            }
        }
        for (position, constructor) in self.constructors.iter().enumerate() {
            if constructor.id.index() != position {
                return Err(Error::plain("malformed constructor id"));
            }
            let family = self
                .inductives
                .get(constructor.inductive.index())
                .ok_or_else(|| Error::plain("constructor references a missing inductive"))?;
            if !family.constructors.ordinary()?.contains(&constructor.id) {
                return Err(Error::plain(
                    "constructor is missing from its inductive family",
                ));
            }
            let parameter_count = family.parameters.len();
            let mut bound = parameter_count;
            let mut actual_recursive = Vec::new();
            for (argument_index, entry) in constructor.arguments.iter().enumerate() {
                self.validate_scoped(entry.ty, bound, 0)?;
                if let Some(arguments) =
                    self.direct_inductive_application(entry.ty, constructor.inductive)
                {
                    if arguments.len() != parameter_count + family.indices.len() {
                        return Err(Error::plain(
                            "recursive argument must apply every parameter and index",
                        ));
                    }
                    for (parameter, argument) in arguments.iter().take(parameter_count).enumerate()
                    {
                        let expected = bound - 1 - parameter;
                        if !matches!(self.terms.get(*argument).term, Term::Var(index) if index == expected)
                        {
                            return Err(Error::plain(
                                "recursive argument changes a uniform parameter",
                            ));
                        }
                    }
                    actual_recursive.push(argument_index);
                } else if self.contains_inductive(entry.ty, constructor.inductive, 0)? {
                    return Err(Error::plain(
                        "nested or negative recursive occurrence is not supported",
                    ));
                }
                bound += 1;
            }
            if actual_recursive != constructor.recursive_arguments {
                return Err(Error::plain(
                    "recursive argument metadata does not match constructor types",
                ));
            }
            if constructor.result_indices.len() != family.indices.len() {
                return Err(Error::plain(
                    "constructor has the wrong number of result indices",
                ));
            }
            for index in &constructor.result_indices {
                self.validate_scoped(*index, bound, 0)?;
                if self.contains_inductive(*index, constructor.inductive, 0)? {
                    return Err(Error::plain(
                        "constructor result index contains the inductive family",
                    ));
                }
            }
        }
        Ok(())
    }

    fn direct_inductive_application(
        &self,
        term: TermId,
        family: InductiveId,
    ) -> Option<Vec<TermId>> {
        let mut cursor = term;
        let mut arguments = Vec::new();
        while let Term::App(function, argument) = self.terms.get(cursor).term {
            arguments.push(argument);
            cursor = function;
        }
        arguments.reverse();
        matches!(self.terms.get(cursor).term, Term::Inductive(id) if id == family)
            .then_some(arguments)
    }

    fn contains_inductive(&self, term: TermId, family: InductiveId, depth: usize) -> Result<bool> {
        if depth > 512 {
            return Err(Error::plain("inductive metadata nesting exceeds 512"));
        }
        let found = match &self.terms.get(term).term {
            Term::Inductive(id) => *id == family,
            Term::Pi(a, b) | Term::Sigma(a, b) | Term::App(a, b) | Term::Ann(a, b) => {
                self.contains_inductive(*a, family, depth + 1)?
                    || self.contains_inductive(*b, family, depth + 1)?
            }
            Term::Path(a, b, c) => {
                self.contains_inductive(*a, family, depth + 1)?
                    || self.contains_inductive(*b, family, depth + 1)?
                    || self.contains_inductive(*c, family, depth + 1)?
            }
            Term::Suc(a) => self.contains_inductive(*a, family, depth + 1)?,
            _ => false,
        };
        Ok(found)
    }

    fn validate_scoped(&self, term: TermId, bound: usize, depth: usize) -> Result<()> {
        if depth > 512 {
            return Err(Error::plain("inductive metadata nesting exceeds 512"));
        }
        match &self.terms.get(term).term {
            Term::Var(index) if *index >= bound => {
                return Err(Error::plain(
                    "inductive metadata contains an escaped variable",
                ));
            }
            Term::Var(_) => {}
            Term::Pi(a, b) | Term::Sigma(a, b) => {
                self.validate_scoped(*a, bound, depth + 1)?;
                self.validate_scoped(*b, bound + 1, depth + 1)?;
            }
            Term::App(a, b) | Term::Ann(a, b) => {
                self.validate_scoped(*a, bound, depth + 1)?;
                self.validate_scoped(*b, bound, depth + 1)?;
            }
            Term::Path(a, b, c) => {
                self.validate_scoped(*a, bound, depth + 1)?;
                self.validate_scoped(*b, bound, depth + 1)?;
                self.validate_scoped(*c, bound, depth + 1)?;
            }
            Term::Suc(a) => self.validate_scoped(*a, bound, depth + 1)?,
            Term::Global(_) => {
                return Err(Error::plain(
                    "global aliases are not allowed in inductive metadata",
                ));
            }
            Term::U(_)
            | Term::Bool
            | Term::True
            | Term::False
            | Term::Nat
            | Term::Inductive(_)
            | Term::Constructor(_)
            | Term::Zero => {}
            _ => return Err(Error::plain("unsupported term in inductive metadata")),
        }
        Ok(())
    }

    pub(crate) fn alloc(&mut self, term: Term, offset: usize) -> TermId {
        self.terms.alloc(Node { term, offset })
    }

    pub(crate) fn push_decl(&mut self, name: String, ty: TermId, body: TermId) {
        self.decls.push(Decl { name, ty, body });
    }

    #[allow(dead_code)]
    pub(crate) fn push_inductive(
        &mut self,
        name: String,
        universe: u32,
        parameters: Telescope,
        indices: Telescope,
    ) -> InductiveId {
        let id = InductiveId::new(self.inductives.len());
        self.inductives.push(InductiveDecl {
            id,
            name,
            universe,
            parameters,
            indices,
            constructors: FamilyConstructors::Ordinary(vec![]),
        });
        id
    }

    #[allow(dead_code)]
    pub(crate) fn push_constructor(
        &mut self,
        inductive: InductiveId,
        name: String,
        arguments: Telescope,
        result_indices: Vec<TermId>,
        recursive_arguments: Vec<usize>,
    ) -> ConstructorId {
        let constructor = ConstructorDecl {
            id: ConstructorId::new(self.constructors.len()),
            inductive,
            name,
            arguments,
            result_indices,
            recursive_arguments,
        };
        self.constructors.push(constructor.clone());
        match &mut self.inductives[inductive.index()].constructors {
            FamilyConstructors::Ordinary(ids) => ids.push(constructor.id),
            FamilyConstructors::Higher(ids) => ids.push(ConstructorRef::Point(constructor.id)),
        }
        constructor.id
    }
}
#[derive(Debug)]
struct S {
    kind: Kind,
    offset: usize,
}
#[derive(Debug)]
enum Kind {
    Atom(String),
    List(Vec<S>),
}
impl S {
    fn atom(&self) -> Result<&str> {
        if let Kind::Atom(a) = &self.kind {
            Ok(a)
        } else {
            Err(Error::at(self.offset, "expected a name"))
        }
    }
    fn list(&self) -> Result<&[S]> {
        if let Kind::List(a) = &self.kind {
            Ok(a)
        } else {
            Err(Error::at(self.offset, "expected a list"))
        }
    }
}
fn sexps(source: &str) -> Result<Vec<S>> {
    fn ws(s: &[u8], i: &mut usize) {
        loop {
            while *i < s.len() && s[*i].is_ascii_whitespace() {
                *i += 1;
            }
            if s.get(*i) == Some(&b';') {
                while *i < s.len() && s[*i] != b'\n' {
                    *i += 1;
                }
            } else {
                break;
            }
        }
    }
    fn one(source: &str, i: &mut usize, depth: usize) -> Result<S> {
        if depth > 512 {
            return Err(Error::at(*i, "syntax nesting exceeds 512"));
        }
        let s = source.as_bytes();
        ws(s, i);
        let offset = *i;
        match s.get(*i) {
            Some(b'(') => {
                *i += 1;
                let mut xs = vec![];
                loop {
                    ws(s, i);
                    match s.get(*i) {
                        Some(b')') => {
                            *i += 1;
                            break;
                        }
                        None => return Err(Error::at(offset, "unclosed list")),
                        _ => xs.push(one(source, i, depth + 1)?),
                    }
                }
                Ok(S {
                    kind: Kind::List(xs),
                    offset,
                })
            }
            Some(b')') => Err(Error::at(offset, "unexpected ')'")),
            Some(_) => {
                while *i < s.len() && !s[*i].is_ascii_whitespace() && !b"();".contains(&s[*i]) {
                    *i += 1;
                }
                Ok(S {
                    kind: Kind::Atom(source[offset..*i].into()),
                    offset,
                })
            }
            None => Err(Error::at(offset, "expected expression")),
        }
    }
    let mut i = 0;
    let mut out = vec![];
    loop {
        ws(source.as_bytes(), &mut i);
        if i == source.len() {
            return Ok(out);
        }
        out.push(one(source, &mut i, 0)?);
    }
}
struct Parser {
    program: Program,
    globals: HashMap<String, usize>,
    terms: Vec<String>,
    dims: Vec<String>,
}
impl Parser {
    fn dim(&self, s: &S) -> Result<D> {
        match s.atom()? {
            "0" => Ok(D::Zero),
            "1" => Ok(D::One),
            n => self
                .dims
                .iter()
                .rev()
                .position(|x| x == n)
                .map(D::Bound)
                .ok_or_else(|| Error::at(s.offset, format!("unknown interval variable '{n}'"))),
        }
    }
    fn face(&self, s: &S) -> Result<F> {
        if let Kind::Atom(n) = &s.kind {
            return match n.as_str() {
                "top" => Ok(F::Top),
                "bottom" => Ok(F::Bot),
                _ => Err(Error::at(s.offset, "expected face formula")),
            };
        }
        let xs = s.list()?;
        if xs.len() != 3 {
            return Err(Error::at(s.offset, "face operator requires two arguments"));
        }
        match xs[0].atom()? {
            "=" => Ok(F::Eq(self.dim(&xs[1])?, self.dim(&xs[2])?)),
            "and" => Ok(F::And(
                Box::new(self.face(&xs[1])?),
                Box::new(self.face(&xs[2])?),
            )),
            "or" => Ok(F::Or(
                Box::new(self.face(&xs[1])?),
                Box::new(self.face(&xs[2])?),
            )),
            _ => Err(Error::at(s.offset, "unknown face operator")),
        }
    }
    fn bind(&mut self, name: &S, body: &S, dim: bool) -> Result<TermId> {
        let n = name.atom()?.to_owned();
        if dim {
            self.dims.push(n);
        } else {
            self.terms.push(n);
        }
        let b = self.term(body);
        if dim {
            self.dims.pop();
        } else {
            self.terms.pop();
        }
        b
    }
    fn term(&mut self, s: &S) -> Result<TermId> {
        let t = match &s.kind {
            Kind::Atom(n) => match n.as_str() {
                "Bool" => Term::Bool,
                "true" => Term::True,
                "false" => Term::False,
                "Nat" => Term::Nat,
                "zero" => Term::Zero,
                _ => {
                    if let Some(i) = self.terms.iter().rev().position(|x| x == n) {
                        Term::Var(i)
                    } else if let Some(i) = self.globals.get(n) {
                        Term::Global(*i)
                    } else {
                        return Err(Error::at(s.offset, format!("unknown name '{n}'")));
                    }
                }
            },
            Kind::List(xs) => {
                if xs.is_empty() {
                    return Err(Error::at(s.offset, "empty expression"));
                }
                let op = xs[0].atom()?;
                let arity = |n: usize| {
                    if xs.len() == n + 1 {
                        Ok(())
                    } else {
                        Err(Error::at(s.offset, format!("'{op}' expects {n} arguments")))
                    }
                };
                match op {
                    "U" => {
                        arity(1)?;
                        Term::U(xs[1].atom()?.parse().map_err(|_| {
                            Error::at(xs[1].offset, "expected a universe level (u32)")
                        })?)
                    }
                    "Pi" | "Sigma" => {
                        arity(3)?;
                        let a = self.term(&xs[2])?;
                        let b = self.bind(&xs[1], &xs[3], false)?;
                        if op == "Pi" {
                            Term::Pi(a, b)
                        } else {
                            Term::Sigma(a, b)
                        }
                    }
                    "lam" => {
                        arity(2)?;
                        Term::Lam(self.bind(&xs[1], &xs[2], false)?)
                    }
                    "app" | "pair" | "ann" => {
                        arity(2)?;
                        let a = self.term(&xs[1])?;
                        let b = self.term(&xs[2])?;
                        match op {
                            "app" => Term::App(a, b),
                            "pair" => Term::Pair(a, b),
                            _ => Term::Ann(a, b),
                        }
                    }
                    "fst" | "snd" | "suc" => {
                        arity(1)?;
                        let a = self.term(&xs[1])?;
                        match op {
                            "fst" => Term::Fst(a),
                            "snd" => Term::Snd(a),
                            _ => Term::Suc(a),
                        }
                    }
                    "bool-elim" | "nat-elim" => {
                        arity(4)?;
                        let p = self.term(&xs[1])?;
                        let a = self.term(&xs[2])?;
                        let b = self.term(&xs[3])?;
                        let c = self.term(&xs[4])?;
                        if op == "bool-elim" {
                            Term::If(p, a, b, c)
                        } else {
                            Term::NatElim(p, a, b, c)
                        }
                    }
                    "Path" => {
                        arity(4)?;
                        let a = self.bind(&xs[1], &xs[2], true)?;
                        let l = self.term(&xs[3])?;
                        let r = self.term(&xs[4])?;
                        Term::Path(a, l, r)
                    }
                    "path" => {
                        arity(2)?;
                        Term::PLam(self.bind(&xs[1], &xs[2], true)?)
                    }
                    "at" => {
                        arity(2)?;
                        Term::PApp(self.term(&xs[1])?, self.dim(&xs[2])?)
                    }
                    "coe" | "com" => {
                        arity(if op == "coe" { 5 } else { 6 })?;
                        let from = self.dim(&xs[3])?;
                        let to = self.dim(&xs[4])?;
                        let cap = self.term(&xs[5])?;
                        let family = self.bind(&xs[1], &xs[2], true)?;
                        let mut tubes = vec![];
                        if op == "com" {
                            for branch in xs[6].list()? {
                                let b = branch.list()?;
                                if b.len() != 2 {
                                    return Err(Error::at(branch.offset, "expected (face body)"));
                                }
                                let f = self.face(&b[0])?;
                                let t = self.bind(&xs[1], &b[1], true)?;
                                tubes.push((f, t));
                            }
                        }
                        Term::Com {
                            family,
                            from,
                            to,
                            cap,
                            tubes,
                        }
                    }
                    "system" => {
                        arity(2)?;
                        let a = self.term(&xs[1])?;
                        let mut bs = vec![];
                        for b in xs[2].list()? {
                            let b = b.list()?;
                            if b.len() != 2 {
                                return Err(Error::at(s.offset, "expected (face body)"));
                            }
                            bs.push((self.face(&b[0])?, self.term(&b[1])?));
                        }
                        Term::System(a, bs)
                    }
                    "Glue" => {
                        arity(2)?;
                        let a = self.term(&xs[1])?;
                        let mut bs = vec![];
                        for branch in xs[2].list()? {
                            let b = branch.list()?;
                            if b.len() != 3 {
                                return Err(Error::at(
                                    branch.offset,
                                    "expected (face type equivalence)",
                                ));
                            }
                            bs.push((self.face(&b[0])?, self.term(&b[1])?, self.term(&b[2])?));
                        }
                        Term::Glue(a, bs)
                    }
                    "glue" => {
                        arity(3)?;
                        let g = self.term(&xs[1])?;
                        let a = self.term(&xs[2])?;
                        let mut bs = vec![];
                        for branch in xs[3].list()? {
                            let b = branch.list()?;
                            if b.len() != 2 {
                                return Err(Error::at(branch.offset, "expected (face term)"));
                            }
                            bs.push((self.face(&b[0])?, self.term(&b[1])?));
                        }
                        Term::GlueIntro(g, a, bs)
                    }
                    "unglue" => {
                        arity(2)?;
                        Term::Unglue(self.term(&xs[1])?, self.term(&xs[2])?)
                    }
                    _ => return Err(Error::at(s.offset, format!("unknown form '{op}'"))),
                }
            }
        };
        Ok(self.program.terms.alloc(Node {
            term: t,
            offset: s.offset,
        }))
    }
}
pub(crate) fn parse(source: &str) -> Result<Program> {
    let mut p = Parser {
        program: Program::default(),
        globals: HashMap::new(),
        terms: vec![],
        dims: vec![],
    };
    for s in sexps(source)? {
        let xs = s.list()?;
        if xs.len() != 4 || xs[0].atom()? != "def" {
            return Err(Error::at(s.offset, "expected (def name type body)"));
        }
        let name = xs[1].atom()?.to_owned();
        if p.globals.contains_key(&name)
            || ["Bool", "Nat", "true", "false", "zero"].contains(&name.as_str())
        {
            return Err(Error::at(
                xs[1].offset,
                "duplicate or reserved declaration name",
            ));
        }
        let ty = p.term(&xs[2])?;
        let body = p.term(&xs[3])?;
        p.globals.insert(name.clone(), p.program.decls.len());
        p.program.decls.push(Decl { name, ty, body });
    }
    Ok(p.program)
}

#[cfg(test)]
mod inductive_metadata_tests {
    use super::*;

    fn entry(program: &mut Program, name: &str, term: Term) -> TelescopeEntry {
        TelescopeEntry {
            name: name.to_owned(),
            ty: program.alloc(term, 0),
        }
    }

    #[test]
    fn stores_nat_shaped_inductive_metadata() {
        let mut program = Program::default();
        let nat = program.push_inductive("UserNat".to_owned(), 0, vec![], vec![]);
        program.push_constructor(nat, "zero".to_owned(), vec![], vec![], vec![]);
        let pred = entry(&mut program, "pred", Term::Inductive(nat));
        program.push_constructor(nat, "suc".to_owned(), vec![pred], vec![], vec![0]);

        let declaration = &program.inductives[nat.index()];
        assert_eq!(declaration.id, nat);
        assert_eq!(declaration.name, "UserNat");
        assert_eq!(declaration.universe, 0);
        assert!(declaration.parameters.is_empty());
        assert!(declaration.indices.is_empty());
        assert_eq!(declaration.constructors.ordinary().unwrap().len(), 2);
        let zero = &program.constructors[declaration.constructors.ordinary().unwrap()[0].index()];
        let suc = &program.constructors[declaration.constructors.ordinary().unwrap()[1].index()];
        assert_eq!(zero.name, "zero");
        assert_eq!(suc.name, "suc");
        assert_eq!(suc.arguments.len(), 1);
        assert_eq!(suc.recursive_arguments, vec![0]);
    }

    #[test]
    fn stores_vec_shaped_parameters_indices_and_constructor_results() {
        let mut program = Program::default();
        let type0 = program.alloc(Term::U(0), 0);
        let nat = program.alloc(Term::Nat, 0);
        let zero = program.alloc(Term::Zero, 0);
        let n = program.alloc(Term::Var(0), 0);
        let suc_n = program.alloc(Term::Suc(n), 0);

        let vec = program.push_inductive(
            "Vec".to_owned(),
            0,
            vec![TelescopeEntry {
                name: "A".to_owned(),
                ty: type0,
            }],
            vec![TelescopeEntry {
                name: "length".to_owned(),
                ty: nat,
            }],
        );
        program.push_constructor(vec, "nil".to_owned(), vec![], vec![zero], vec![]);
        program.push_constructor(
            vec,
            "cons".to_owned(),
            vec![TelescopeEntry {
                name: "n".to_owned(),
                ty: nat,
            }],
            vec![suc_n],
            vec![2],
        );

        let declaration = &program.inductives[vec.index()];
        assert_eq!(declaration.parameters.len(), 1);
        assert_eq!(declaration.indices.len(), 1);
        let nil = &program.constructors[declaration.constructors.ordinary().unwrap()[0].index()];
        let cons = &program.constructors[declaration.constructors.ordinary().unwrap()[1].index()];
        assert_eq!(nil.result_indices.len(), 1);
        assert_eq!(cons.result_indices.len(), 1);
        assert_eq!(nil.id.index(), 0);
        assert_eq!(cons.id.index(), 1);
        assert_eq!(program.constructors.len(), 2);
    }

    #[test]
    fn trusted_validation_rejects_forged_recursive_metadata() {
        let mut program = Program::default();
        let family = program.push_inductive("D".to_owned(), 0, vec![], vec![]);
        let recursive = entry(&mut program, "value", Term::Inductive(family));
        program.push_constructor(family, "step".to_owned(), vec![recursive], vec![], vec![]);
        assert!(
            program
                .validate_inductives()
                .unwrap_err()
                .message
                .contains("recursive argument metadata")
        );
    }

    #[test]
    fn trusted_validation_rejects_negative_occurrences() {
        let mut program = Program::default();
        let family = program.push_inductive("D".to_owned(), 0, vec![], vec![]);
        let domain = program.alloc(Term::Inductive(family), 0);
        let nat = program.alloc(Term::Nat, 0);
        let negative = program.alloc(Term::Pi(domain, nat), 0);
        let argument = TelescopeEntry {
            name: "f".to_owned(),
            ty: negative,
        };
        program.push_constructor(family, "bad".to_owned(), vec![argument], vec![], vec![]);
        assert!(
            program
                .validate_inductives()
                .unwrap_err()
                .message
                .contains("negative")
        );
    }

    #[test]
    fn trusted_validation_rejects_global_aliases_that_could_hide_negativity() {
        let mut program = Program::default();
        let family = program.push_inductive("D".to_owned(), 0, vec![], vec![]);
        let universe = program.alloc(Term::U(0), 0);
        let recursive = program.alloc(Term::Inductive(family), 0);
        let nat = program.alloc(Term::Nat, 0);
        let negative_alias = program.alloc(Term::Pi(recursive, nat), 0);
        program.push_decl("Neg".to_owned(), universe, negative_alias);
        let alias = program.alloc(Term::Global(0), 0);
        program.push_constructor(
            family,
            "bad".to_owned(),
            vec![TelescopeEntry {
                name: "hidden".to_owned(),
                ty: alias,
            }],
            vec![],
            vec![],
        );
        assert!(
            program
                .validate_inductives()
                .unwrap_err()
                .message
                .contains("global aliases")
        );
    }
}
