use super::ast::{
    ConstructorDeclaration, DataDeclaration, Declaration, Expr, Item, MatchBranch, Pattern, Program,
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
            b'=' => (TokenKind::Eq, 1),
            _ => {
                let start = i;
                while !(i >= bytes.len()
                    || bytes[i].is_ascii_whitespace()
                    || b"(){}:=\\;".contains(&bytes[i])
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
        let left = self.application()?;
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

    fn application(&mut self) -> Result<Expr> {
        let mut expr = self.atom()?;
        while self.starts_atom() {
            let argument = self.atom()?;
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
                "def" | "data" | "module" | "import" | "where" | "let"
            ),
            _ => false,
        }
    }

    fn atom(&mut self) -> Result<Expr> {
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
                indices.push((
                    parameter.unwrap_or_else(|| format!("_index{}", indices.len())),
                    *domain,
                ));
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
        arguments.push((
            parameter.unwrap_or_else(|| format!("_arg{}", arguments.len())),
            *domain,
        ));
        ty = *codomain;
    }
    (arguments, ty)
}
