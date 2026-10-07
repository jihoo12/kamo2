use super::ast::{
    ConstructorDeclaration, DataDeclaration, Declaration, Dimension, Expr, Item, MatchBranch,
    Pattern, Program,
};
use crate::{Error, Result};

#[derive(Clone, Debug, PartialEq, Eq)]
enum TokenKind {
    Name(String),
    LParen,
    RParen,
    LBrace,
    RBrace,
    Colon,
    Eq,
    EqualEqual,
    At,
    Arrow,
    FatArrow,
    Backslash,
    Semicolon,
}

#[derive(Clone, Debug)]
struct Token {
    kind: TokenKind,
    offset: usize,
}

fn lex(source: &str) -> Result<Vec<Token>> {
    let bytes = source.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i].is_ascii_whitespace() {
            i += 1;
            continue;
        }
        if bytes[i] == b'#' {
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        let offset = i;
        let (kind, width) = match bytes[i] {
            b'(' => (TokenKind::LParen, 1),
            b')' => (TokenKind::RParen, 1),
            b'{' => (TokenKind::LBrace, 1),
            b'}' => (TokenKind::RBrace, 1),
            b':' => (TokenKind::Colon, 1),
            b'\\' => (TokenKind::Backslash, 1),
            b';' => (TokenKind::Semicolon, 1),
            b'-' if bytes.get(i + 1) == Some(&b'>') => (TokenKind::Arrow, 2),
            b'=' if bytes.get(i + 1) == Some(&b'>') => (TokenKind::FatArrow, 2),
            b'=' if bytes.get(i + 1) == Some(&b'=') => (TokenKind::EqualEqual, 2),
            b'@' => (TokenKind::At, 1),
            b'=' => (TokenKind::Eq, 1),
            _ => {
                let start = i;
                while !(i >= bytes.len()
                    || bytes[i].is_ascii_whitespace()
                    || b"(){}:=@\\;".contains(&bytes[i])
                    || bytes[i] == b'-' && bytes.get(i + 1) == Some(&b'>'))
                {
                    i += 1;
                }
                if start == i {
                    return Err(Error::at(offset, "unexpected character"));
                }
                out.push(Token {
                    kind: TokenKind::Name(source[start..i].to_owned()),
                    offset,
                });
                continue;
            }
        };
        out.push(Token { kind, offset });
        i += width;
    }
    Ok(out)
}

pub fn parse(source: &str) -> Result<Program> {
    let mut parser = Parser {
        tokens: lex(source)?,
        index: 0,
    };
    parser.program()
}

struct Parser {
    tokens: Vec<Token>,
    index: usize,
}

impl Parser {
    fn offset(&self) -> usize {
        self.tokens.get(self.index).map_or(0, |t| t.offset)
    }

    fn peek_name(&self, name: &str) -> bool {
        matches!(self.tokens.get(self.index), Some(Token { kind: TokenKind::Name(n), .. }) if n == name)
    }

    fn eat(&mut self, kind: &TokenKind) -> bool {
        if self.tokens.get(self.index).is_some_and(|t| &t.kind == kind) {
            self.index += 1;
            true
        } else {
            false
        }
    }

    fn name(&mut self) -> Result<String> {
        match self.tokens.get(self.index) {
            Some(Token {
                kind: TokenKind::Name(name),
                ..
            }) => {
                let name = name.clone();
                self.index += 1;
                Ok(name)
            }
            _ => Err(Error::at(self.offset(), "expected a name")),
        }
    }

    fn expect(&mut self, kind: TokenKind, message: &str) -> Result<()> {
        if self.eat(&kind) {
            Ok(())
        } else {
            Err(Error::at(self.offset(), message))
        }
    }

    fn program(&mut self) -> Result<Program> {
        let module = if self.peek_name("module") {
            self.index += 1;
            let name = self.name()?;
            self.eat(&TokenKind::Semicolon);
            Some(name)
        } else {
            None
        };
        let mut imports = Vec::new();
        while self.peek_name("import") {
            self.index += 1;
            imports.push(self.name()?);
            self.eat(&TokenKind::Semicolon);
        }
        let mut declarations = Vec::new();
        while self.index < self.tokens.len() {
            if self.peek_name("def") {
                self.index += 1;
                declarations.push(Item::Definition(self.declaration()?));
            } else if self.peek_name("data") {
                self.index += 1;
                declarations.push(Item::Data(self.data_declaration()?));
            } else {
                return Err(Error::at(self.offset(), "expected 'def' or 'data'"));
            }
            self.eat(&TokenKind::Semicolon);
        }
        Ok(Program {
            module,
            imports,
            declarations,
        })
    }

    fn binder(&mut self) -> Result<(String, Expr)> {
        self.expect(TokenKind::LParen, "expected '('")?;
        let name = self.name()?;
        self.expect(TokenKind::Colon, "expected ':' in binder")?;
        let ty = self.expr()?;
        self.expect(TokenKind::RParen, "expected ')' after binder")?;
        Ok((name, ty))
    }

    fn data_declaration(&mut self) -> Result<DataDeclaration> {
        let name = self.name()?;
        let mut parameters = Vec::new();
        while matches!(
            self.tokens.get(self.index).map(|t| &t.kind),
            Some(TokenKind::LParen)
        ) {
            parameters.push(self.binder()?);
        }
        self.expect(TokenKind::Colon, "expected ':' after data header")?;
        let kind = self.expr()?;
        let (indices, universe) = split_kind(kind)?;
        if !self.peek_name("where") {
            return Err(Error::at(self.offset(), "expected 'where'"));
        }
        self.index += 1;
        self.expect(TokenKind::LBrace, "expected '{' after 'where'")?;
        let mut constructors = Vec::new();
        while !self.eat(&TokenKind::RBrace) {
            let constructor_name = self.name()?;
            self.expect(TokenKind::Colon, "expected ':' after constructor name")?;
            let ty = self.expr()?;
            let (arguments, result) = split_constructor(ty);
            constructors.push(ConstructorDeclaration {
                name: constructor_name,
                arguments,
                result,
            });
            if !matches!(
                self.tokens.get(self.index).map(|token| &token.kind),
                Some(TokenKind::RBrace)
            ) {
                self.expect(TokenKind::Semicolon, "expected ';' between constructors")?;
            }
        }
        Ok(DataDeclaration {
            name,
            parameters,
            indices,
            universe,
            constructors,
        })
    }

    fn declaration(&mut self) -> Result<Declaration> {
        let name = self.name()?;
        let mut parameters = Vec::new();
        while self.eat(&TokenKind::LParen) {
            let parameter = self.name()?;
            self.expect(TokenKind::Colon, "expected ':' in parameter")?;
            let ty = self.expr()?;
            self.expect(TokenKind::RParen, "expected ')' after parameter")?;
            parameters.push((parameter, ty));
        }
        self.expect(
            TokenKind::Colon,
            "surface definitions require a type annotation",
        )?;
        let mut ty = self.expr()?;
        self.expect(TokenKind::Eq, "expected '=' before definition body")?;
        let mut value = self.expr()?;

        for (parameter, domain) in parameters.into_iter().rev() {
            ty = Expr::Pi {
                parameter: Some(parameter.clone()),
                domain: Box::new(domain),
                codomain: Box::new(ty),
            };
            value = Expr::Lambda {
                parameter,
                body: Box::new(value),
            };
        }
        Ok(Declaration {
            name,
            ty: Some(ty),
            value,
        })
    }

    fn expr(&mut self) -> Result<Expr> {
        if self.peek_name("path") {
            self.index += 1;
            let dimension = self.dimension()?;
            let Dimension::Name(dimension) = dimension else {
                return Err(Error::at(
                    self.offset(),
                    "path binder must be a dimension name",
                ));
            };
            self.expect(TokenKind::FatArrow, "expected '=>' after path dimension")?;
            return Ok(Expr::PathLambda {
                dimension,
                body: Box::new(self.expr()?),
            });
        }
        if self.eat(&TokenKind::Backslash) {
            let parameter = self.name()?;
            self.expect(TokenKind::FatArrow, "expected '=>' after lambda parameter")?;
            return Ok(Expr::Lambda {
                parameter,
                body: Box::new(self.expr()?),
            });
        }
        if self.peek_name("match") {
            self.index += 1;
            let scrutinee = self.arrow()?;
            self.expect(TokenKind::LBrace, "expected '{' after match scrutinee")?;
            let mut branches = Vec::new();
            while !self.eat(&TokenKind::RBrace) {
                let pattern = self.pattern()?;
                self.expect(TokenKind::FatArrow, "expected '=>' after match pattern")?;
                let body = self.expr()?;
                branches.push(MatchBranch { pattern, body });
                if self.eat(&TokenKind::RBrace) {
                    break;
                }
                self.expect(TokenKind::Semicolon, "expected ';' between match branches")?;
            }
            return Ok(Expr::Match {
                scrutinee: Box::new(scrutinee),
                branches,
            });
        }
        if self.peek_name("let") {
            self.index += 1;
            let name = self.name()?;
            self.expect(TokenKind::Eq, "expected '=' in let expression")?;
            let value = self.expr()?;
            self.expect(TokenKind::Semicolon, "expected ';' in let expression")?;
            let body = self.expr()?;
            return Ok(Expr::Let {
                name,
                value: Box::new(value),
                body: Box::new(body),
            });
        }
        self.arrow()
    }

    fn pattern(&mut self) -> Result<Pattern> {
        let name = self.name()?;
        let mut arguments = Vec::new();
        while matches!(
            self.tokens.get(self.index).map(|token| &token.kind),
            Some(TokenKind::Name(_))
        ) {
            arguments.push(Pattern::Name(self.name()?));
        }
        Ok(Pattern::Constructor { name, arguments })
    }

    fn arrow(&mut self) -> Result<Expr> {
        let left = self.equality()?;
        if self.eat(&TokenKind::Arrow) {
            Ok(Expr::Pi {
                parameter: None,
                domain: Box::new(left),
                codomain: Box::new(self.expr()?),
            })
        } else {
            Ok(left)
        }
    }

    // Precedence (tightest first): postfix @, application, non-associative
    // equality, right-associative arrow. Lambda/path bodies extend to the right.
    fn equality(&mut self) -> Result<Expr> {
        let left = self.application()?;
        if !self.eat(&TokenKind::EqualEqual) {
            return Ok(left);
        }
        let right = self.application()?;
        if self.eat(&TokenKind::EqualEqual) {
            return Err(Error::at(
                self.offset(),
                "parenthesize chained path equalities",
            ));
        }
        Ok(Expr::Equality {
            left: Box::new(left),
            right: Box::new(right),
        })
    }

    fn dimension(&mut self) -> Result<Dimension> {
        let offset = self.offset();
        let name = self
            .name()
            .map_err(|_| Error::at(offset, "expected dimension 0, 1, or a name"))?;
        match name.as_str() {
            "0" => Ok(Dimension::Zero),
            "1" => Ok(Dimension::One),
            _ if name
                .chars()
                .next()
                .is_some_and(|c| c.is_alphabetic() || c == '_')
                && name.chars().all(|c| c.is_alphanumeric() || c == '_')
                && !matches!(
                    name.as_str(),
                    "path"
                        | "coe"
                        | "PathP"
                        | "def"
                        | "let"
                        | "match"
                        | "data"
                        | "where"
                        | "module"
                        | "import"
                ) =>
            {
                Ok(Dimension::Name(name))
            }
            _ => Err(Error::at(offset, "expected dimension 0, 1, or a name")),
        }
    }

    fn postfix(&mut self) -> Result<Expr> {
        let mut expr = self.atom()?;
        while self.eat(&TokenKind::At) {
            expr = Expr::PathApply {
                path: Box::new(expr),
                dimension: self.dimension()?,
            };
        }
        Ok(expr)
    }

    fn application(&mut self) -> Result<Expr> {
        let mut expr = self.postfix()?;
        while self.starts_atom() {
            let argument = self.postfix()?;
            expr = Expr::Apply {
                function: Box::new(expr),
                argument: Box::new(argument),
            };
        }
        Ok(expr)
    }

    fn starts_atom(&self) -> bool {
        match self.tokens.get(self.index).map(|t| &t.kind) {
            Some(TokenKind::LParen) => true,
            Some(TokenKind::Name(name)) => !matches!(
                name.as_str(),
                "def" | "data" | "module" | "import" | "where" | "let" | "path"
            ),
            _ => false,
        }
    }

    fn atom(&mut self) -> Result<Expr> {
        if self.peek_name("PathP") {
            self.index += 1;
            self.expect(TokenKind::LParen, "expected '(i => family)' after PathP")?;
            let Dimension::Name(dimension) = self.dimension()? else {
                return Err(Error::at(
                    self.offset(),
                    "PathP binder must be a dimension name",
                ));
            };
            self.expect(TokenKind::FatArrow, "expected '=>' after PathP dimension")?;
            let family = self.expr()?;
            self.expect(TokenKind::RParen, "expected ')' after PathP family")?;
            let left = self.postfix()?;
            let right = self.postfix()?;
            return Ok(Expr::PathP {
                dimension,
                family: Box::new(family),
                left: Box::new(left),
                right: Box::new(right),
            });
        }
        if self.peek_name("coe") {
            self.index += 1;
            self.expect(TokenKind::LParen, "expected '(i => family)' after coe")?;
            let Dimension::Name(dimension) = self.dimension()? else {
                return Err(Error::at(
                    self.offset(),
                    "coe binder must be a dimension name",
                ));
            };
            self.expect(TokenKind::FatArrow, "expected '=>' after coe dimension")?;
            let family = self.expr()?;
            self.expect(TokenKind::RParen, "expected ')' after coe family")?;
            let from = self.dimension()?;
            let to = self.dimension()?;
            let cap = self.postfix()?;
            return Ok(Expr::Coe {
                dimension,
                family: Box::new(family),
                from,
                to,
                cap: Box::new(cap),
            });
        }
        if self.eat(&TokenKind::LParen) {
            let save = self.index;
            if let Ok(parameter) = self.name()
                && self.eat(&TokenKind::Colon)
            {
                let domain = self.expr()?;
                self.expect(TokenKind::RParen, "expected ')' after dependent parameter")?;
                self.expect(TokenKind::Arrow, "expected '->' after dependent parameter")?;
                return Ok(Expr::Pi {
                    parameter: Some(parameter),
                    domain: Box::new(domain),
                    codomain: Box::new(self.expr()?),
                });
            }
            self.index = save;
            let expr = self.expr()?;
            self.expect(TokenKind::RParen, "expected ')'")?;
            return Ok(expr);
        }

        let offset = self.offset();
        let name = self.name()?;
        if name == "path" {
            return Err(Error::at(
                offset,
                "parenthesize a path abstraction in an application",
            ));
        }
        Ok(match name.as_str() {
            "Type" => Expr::Universe(0),
            _ if name.starts_with("Type") && name.len() > 4 => {
                let level = name[4..]
                    .parse()
                    .map_err(|_| Error::at(offset, "invalid universe level"))?;
                Expr::Universe(level)
            }
            _ => Expr::Name(name),
        })
    }
}

fn split_kind(mut kind: Expr) -> Result<(Vec<(String, Expr)>, u32)> {
    let mut indices = Vec::new();
    loop {
        match kind {
            Expr::Universe(level) => return Ok((indices, level)),
            Expr::Pi {
                parameter,
                domain,
                codomain,
            } => {
                indices.push((parameter.unwrap_or_default(), *domain));
                kind = *codomain;
            }
            _ => return Err(Error::plain("data kind must end in Type")),
        }
    }
}

fn split_constructor(mut ty: Expr) -> (Vec<(String, Expr)>, Expr) {
    let mut arguments = Vec::new();
    while let Expr::Pi {
        parameter,
        domain,
        codomain,
    } = ty
    {
        arguments.push((parameter.unwrap_or_default(), *domain));
        ty = *codomain;
    }
    (arguments, ty)
}

#[cfg(test)]
mod path_tests {
    use super::*;

    fn expression(source: &str) -> Expr {
        let mut parser = Parser {
            tokens: lex(source).unwrap(),
            index: 0,
        };
        let expr = parser.expr().unwrap();
        assert_eq!(parser.index, parser.tokens.len());
        expr
    }

    fn name(n: &str) -> Expr {
        Expr::Name(n.to_owned())
    }

    fn apply(f: Expr, x: Expr) -> Expr {
        Expr::Apply {
            function: Box::new(f),
            argument: Box::new(x),
        }
    }

    fn at(p: Expr, dimension: Dimension) -> Expr {
        Expr::PathApply {
            path: Box::new(p),
            dimension,
        }
    }

    #[test]
    fn equality_tokens_and_application_precedence() {
        assert_eq!(
            expression("f x==g y"),
            Expr::Equality {
                left: Box::new(apply(name("f"), name("x"))),
                right: Box::new(apply(name("g"), name("y"))),
            }
        );
        assert_eq!(
            expression("x == y"),
            Expr::Equality {
                left: Box::new(name("x")),
                right: Box::new(name("y")),
            }
        );
        let tokens = lex("x==y=z@0")
            .unwrap()
            .into_iter()
            .map(|t| t.kind)
            .collect::<Vec<_>>();
        assert_eq!(
            tokens,
            vec![
                TokenKind::Name("x".into()),
                TokenKind::EqualEqual,
                TokenKind::Name("y".into()),
                TokenKind::Eq,
                TokenKind::Name("z".into()),
                TokenKind::At,
                TokenKind::Name("0".into())
            ]
        );
    }

    #[test]
    fn path_application_is_postfix_and_dimensions_are_explicit() {
        let pi = at(name("p"), Dimension::Name("i".into()));
        assert_eq!(expression("p @ i"), pi);
        assert_eq!(expression("f (p @ i)"), apply(name("f"), pi.clone()));
        assert_eq!(expression("f p@i"), apply(name("f"), pi));
        assert_eq!(
            expression("(f x)@0@1"),
            at(
                at(apply(name("f"), name("x")), Dimension::Zero),
                Dimension::One
            )
        );
        assert_eq!(
            expression("path i => p@i"),
            Expr::PathLambda {
                dimension: "i".into(),
                body: Box::new(at(name("p"), Dimension::Name("i".into()))),
            }
        );
    }

    #[test]
    fn equality_binds_more_tightly_than_arrow() {
        assert_eq!(
            expression("x == y -> z == w"),
            Expr::Pi {
                parameter: None,
                domain: Box::new(Expr::Equality {
                    left: Box::new(name("x")),
                    right: Box::new(name("y"))
                }),
                codomain: Box::new(Expr::Equality {
                    left: Box::new(name("z")),
                    right: Box::new(name("w"))
                }),
            }
        );
    }

    #[test]
    fn invalid_dimensions_and_chained_equalities_are_rejected() {
        for source in [
            "p @ 2",
            "p @ (i)",
            "p @ i-j",
            "p @",
            "path 0 => x",
            "path 1 => x",
            "path => x",
            "x == y == z",
        ] {
            let mut parser = Parser {
                tokens: lex(source).unwrap(),
                index: 0,
            };
            assert!(parser.expr().is_err(), "{source}");
        }
    }
}
