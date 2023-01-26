use std::collections::LinkedList;

use crate::tokenize::Token;

#[derive(Debug, Clone, PartialEq)]
pub enum Expression {
    Universe,
    UnitType,
    UnitElement,
    Pi(Pattern, Box<Self>, Box<Self>),
    Sigma(Pattern, Box<Self>, Box<Self>),
    Sum(Index, Choices),
    Fun(Index, Choices),
    Construct(Constructor, Box<Self>),
    Lambda(Pattern, Box<Self>),
    Apply(Box<Self>, Box<Self>),
    Pair(Box<Self>, Box<Self>),
    First(Box<Self>),
    Second(Box<Self>),
    Variable(String),
    Declaration(Box<Declaration>, Box<Self>),
}

pub type Constructor = String;

/// This is used for readback, and is arbitrary as long as it is unique.
/// This implementation assigns it the number of subsequent unparsed tokens.
pub type Index = usize;

#[derive(Debug, Clone, PartialEq)]
pub struct Choices(LinkedList<(Constructor, Expression)>);

impl Choices {
    const fn empty() -> Self {
        Self(LinkedList::new())
    }

    fn push_front(self, con: Constructor, expr: Expression) -> Self {
        let Self(mut list) = self;
        list.push_front((con, expr));
        Self(list)
    }

    pub fn get<'a>(&'a self, choice: &str) -> &'a Expression {
        self.0
            .iter()
            .find(|entry| entry.0 == choice)
            .map(|entry| &entry.1)
            .unwrap()
    }

    pub fn is_same_struct(&self, other: &Self) -> bool {
        self.0
            .iter()
            .zip(other.0.iter())
            .all(|((c1, _), (c2, _))| c1 == c2)
    }

    pub fn iter(&self) -> impl Iterator<Item = &(Constructor, Expression)> {
        self.0.iter()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Declaration {
    Define(Pattern, Expression, Expression),
    DefineRec(Pattern, Expression, Expression),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
    Unit,
    Var(String),
    Pair(Box<Self>, Box<Self>),
}

impl Pattern {
    pub fn contains(&self, name: &str) -> bool {
        match self {
            Pattern::Unit => false,
            Pattern::Var(var) => var == name,
            Pattern::Pair(a, b) => a.contains(name) || b.contains(name),
        }
    }
}

fn consume(tokens: &[Token], token: Token) -> Option<&[Token]> {
    match tokens {
        [t, rest @ ..] if *t == token => Some(rest),
        _ => None,
    }
}

fn parse_pattern_single(tokens: &[Token]) -> Option<(Pattern, &[Token])> {
    match tokens {
        [Token::Ident(ident), rest @ ..] => Some((Pattern::Var(ident.clone()), rest)),
        [Token::Underscore, rest @ ..] => Some((Pattern::Unit, rest)),
        _ => None,
    }
}

fn parse_pattern(tokens: &[Token]) -> Option<(Pattern, &[Token])> {
    let (mut pattern, mut rest) = parse_pattern_single(tokens)?;
    while let Some(rest2) = consume(rest, Token::Comma) {
        let (pattern2, rest3) = parse_pattern_single(rest2)?;
        rest = rest3;
        pattern = Pattern::Pair(Box::new(pattern), Box::new(pattern2));
    }
    Some((pattern, rest))
}

/*
fn parse_choices_plain(tokens: &[Token]) -> Option<(Choices, &[Token])> {
    let rest = consume(tokens, Token::ParL)?;
    match rest {
        [Token::Ident(con), rest @ ..] => {
            let (expr, rest) = parse_expression(rest)?;
            let rest = consume(rest, Token::Comma)?;
            let (choices, rest) = parse_choices(rest)?;
            let rest = consume(rest, Token::ParR)?;
            Some((choices.push_front(con.clone(), expr), rest))
        }
        rest => {
            let rest = consume(rest, Token::ParR)?;
            Some((Choices::empty(), rest))
        }
    }
}
*/

fn parse_data(tokens: &[Token]) -> Option<(Choices, &[Token])> {
    match tokens {
        [Token::Ident(con), rest @ ..] => {
            let (expr, rest) = parse_expression(rest).unwrap_or((Expression::UnitType, rest));
            let (choices, rest) = consume(rest, Token::VerticalBar)
                .and_then(parse_data)
                .unwrap_or((Choices::empty(), rest));
            Some((choices.push_front(con.clone(), expr), rest))
        }
        _ => None,
    }
}

fn parse_cases(tokens: &[Token]) -> Option<(Choices, &[Token])> {
    match tokens {
        [Token::Ident(con), rest @ ..] => {
            let (pat, rest) = parse_pattern(rest).unwrap_or((Pattern::Unit, rest));
            let rest = consume(rest, Token::CaseArrow)?;
            let (expr, rest) = parse_expression(rest)?;
            let (choices, rest) = consume(rest, Token::VerticalBar)
                .and_then(parse_cases)
                .unwrap_or((Choices::empty(), rest));
            Some((
                choices.push_front(con.clone(), Expression::Lambda(pat, Box::new(expr))),
                rest,
            ))
        }
        _ => None,
    }
}

fn parse_choices(tokens: &[Token]) -> Option<(Choices, &[Token])> {
    let rest = consume(tokens, Token::ParL)?;
    let (choices, rest) = parse_cases(rest).or(parse_data(rest))?;
    let rest = consume(rest, Token::ParR)?;
    Some((choices, rest))
}

fn parse_expression_strong(tokens: &[Token]) -> Option<(Expression, &[Token])> {
    match tokens {
        [Token::Lambda, rest @ ..] => {
            let (pat, rest) = parse_pattern(rest)?;
            let rest = consume(rest, Token::Dot)?;
            let (expr, rest) = parse_expression(rest)?;
            Some((Expression::Lambda(pat, Box::new(expr)), rest))
        }
        [Token::Ident(ident), rest @ ..] => {
            if ident.starts_with(char::is_uppercase) {
                let (expr, rest) =
                    parse_expression(rest).unwrap_or((Expression::UnitElement, rest));
                Some((Expression::Construct(ident.clone(), Box::new(expr)), rest))
            } else {
                Some((Expression::Variable(ident.clone()), rest))
            }
        }
        [Token::Pi, rest @ ..] => {
            let (pat, rest) = parse_pattern(rest)?;
            let rest = consume(rest, Token::Colon)?;
            let (a, rest) = parse_expression(rest)?;
            let rest = consume(rest, Token::Dot)?;
            let (b, rest) = parse_expression(rest)?;
            Some((Expression::Pi(pat, Box::new(a), Box::new(b)), rest))
        }
        [Token::Sigma, rest @ ..] => {
            let (pat, rest) = parse_pattern(rest)?;
            let rest = consume(rest, Token::Colon)?;
            let (a, rest) = parse_expression(rest)?;
            let rest = consume(rest, Token::Dot)?;
            let (b, rest) = parse_expression(rest)?;
            Some((Expression::Sigma(pat, Box::new(a), Box::new(b)), rest))
        }
        [Token::Universe, rest @ ..] => Some((Expression::Universe, rest)),
        [Token::Zero, rest @ ..] => Some((Expression::UnitElement, rest)),
        [Token::One, rest @ ..] => Some((Expression::UnitType, rest)),
        [Token::Fun, rest @ ..] => {
            let (choices, rest) = parse_choices(rest)?;
            Some((Expression::Fun(rest.len(), choices), rest))
        }
        [Token::Sum, rest @ ..] => {
            let (choices, rest) = parse_choices(rest)?;
            Some((Expression::Sum(rest.len(), choices), rest))
        }
        [Token::ParL, rest @ ..] => {
            let (expr, rest) = parse_expression(rest)?;
            let rest = consume(rest, Token::ParR)?;
            Some((expr, rest))
        }
        _ => None,
    }
}

fn parse_pair_field(tokens: &[Token]) -> Option<(Expression, &[Token])> {
    let (expr, rest) = parse_expression_strong(tokens)?;
    match rest {
        [Token::Dot, Token::One, rest @ ..] => Some((Expression::First(Box::new(expr)), rest)),
        [Token::Dot, Token::Two, rest @ ..] => Some((Expression::Second(Box::new(expr)), rest)),
        _ => Some((expr, rest)),
    }
}

fn parse_application(tokens: &[Token]) -> Option<(Expression, &[Token])> {
    let (mut expr, mut rest) = parse_pair_field(tokens)?;
    while let Some((arg, rest2)) = parse_pair_field(rest) {
        expr = Expression::Apply(Box::new(expr), Box::new(arg));
        rest = rest2;
    }
    Some((expr, rest))
}

fn parse_cross(tokens: &[Token]) -> Option<(Expression, &[Token])> {
    let (expr1, rest) = parse_application(tokens)?;
    match consume(rest, Token::Cross).and_then(parse_expression) {
        Some((expr2, rest)) => Some((
            Expression::Sigma(Pattern::Unit, Box::new(expr1), Box::new(expr2)),
            rest,
        )),
        None => Some((expr1, rest)),
    }
}

fn parse_pair(tokens: &[Token]) -> Option<(Expression, &[Token])> {
    let (expr1, rest) = parse_cross(tokens)?;
    match consume(rest, Token::Comma).and_then(parse_expression) {
        Some((expr2, rest)) => Some((Expression::Pair(Box::new(expr1), Box::new(expr2)), rest)),
        None => Some((expr1, rest)),
    }
}

fn parse_arrow(tokens: &[Token]) -> Option<(Expression, &[Token])> {
    let (expr1, rest) = parse_pair(tokens)?;
    match consume(rest, Token::Arrow).and_then(parse_expression) {
        Some((expr2, rest)) => Some((
            Expression::Pi(Pattern::Unit, Box::new(expr1), Box::new(expr2)),
            rest,
        )),
        None => Some((expr1, rest)),
    }
}

fn parse_expression(tokens: &[Token]) -> Option<(Expression, &[Token])> {
    parse_arrow(tokens)
}

fn parse_declaration(tokens: &[Token]) -> Option<(Declaration, &[Token])> {
    match tokens {
        [Token::Let, Token::Rec, rest @ ..] => {
            let (pat, rest) = parse_pattern(rest)?;
            let rest = consume(rest, Token::Colon)?;
            let (ty, rest) = parse_expression(rest)?;
            let rest = consume(rest, Token::Assign)?;
            let (expr, rest) = parse_expression(rest)?;
            Some((Declaration::DefineRec(pat, ty, expr), rest))
        }
        [Token::Let, rest @ ..] => {
            let (pat, rest) = parse_pattern(rest)?;
            let rest = consume(rest, Token::Colon)?;
            let (ty, rest) = parse_expression(rest)?;
            let rest = consume(rest, Token::Assign)?;
            let (expr, rest) = parse_expression(rest)?;
            Some((Declaration::Define(pat, ty, expr), rest))
        }
        _ => None,
    }
}

fn parse_declarations(tokens: &[Token]) -> Option<(Expression, &[Token])> {
    let (decl, rest) = parse_declaration(tokens)?;
    let rest = consume(rest, Token::Semicolon)?;
    let (expr, rest) = parse_declarations(rest).unwrap_or((Expression::UnitElement, rest));
    Some((
        Expression::Declaration(Box::new(decl), Box::new(expr)),
        rest,
    ))
}

pub fn parse(tokens: &[Token]) -> Option<(Expression, &[Token])> {
    parse_declarations(tokens)
}
