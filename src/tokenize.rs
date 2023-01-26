use std::collections::LinkedList;

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    Lambda,
    Dot,
    Comma,
    Pi,
    Sigma,
    Arrow,
    CaseArrow,
    Cross,
    VerticalBar,
    Fun,
    Sum,
    Colon,
    Semicolon,
    Universe,
    Zero,
    One,
    Two,
    ParL,
    ParR,
    Underscore,
    Assign,
    Let,
    Rec,
    Ident(String),
}

pub fn tokenize(src: &str) -> LinkedList<Token> {
    if src.is_empty() {
        return LinkedList::new();
    }

    if src.starts_with(char::is_whitespace) {
        return tokenize(&src[1..]);
    }

    if src.starts_with("//") {
        return match src.find('\n') {
            Some(at) => tokenize(&src[(at + 1)..]),
            None => tokenize(""),
        };
    }

    if src.starts_with("/*") {
        return match src.find("*/") {
            Some(at) => tokenize(&src[(at + 2)..]),
            None => tokenize(""),
        };
    }

    // The symbols sorted by length.
    let symbols = [
        ("\\lambda", Token::Lambda),
        ("\\sigma", Token::Sigma),
        ("\\pi", Token::Pi),
        ("->", Token::Arrow),
        ("=>", Token::CaseArrow),
        ("λ", Token::Lambda),
        ("Π", Token::Pi),
        ("∑", Token::Sigma),
        ("→", Token::Arrow),
        ("×", Token::Cross),
        ("|", Token::VerticalBar),
        (":", Token::Colon),
        (";", Token::Semicolon),
        ("(", Token::ParL),
        (")", Token::ParR),
        ("_", Token::Underscore),
        ("=", Token::Assign),
        (".", Token::Dot),
        (",", Token::Comma),
    ];

    for (sym, token) in symbols {
        if src.starts_with(sym) {
            let mut tokens = tokenize(&src[(sym.len())..]);
            tokens.push_front(token);
            return tokens;
        }
    }

    // The keywords sorted by length.
    let keywords = [
        ("let", Token::Let),
        ("rec", Token::Rec),
        ("fun", Token::Fun),
        ("Sum", Token::Sum),
        ("U", Token::Universe),
        ("0", Token::Zero),
        ("1", Token::One),
        ("2", Token::Two),
    ];

    fn is_ident_character(c: &char) -> bool {
        c.is_alphanumeric() || *c == '_' || *c == '-' || *c == '\''
    }

    let ident: String = src.chars().take_while(is_ident_character).collect();

    assert!(ident.len() > 0);

    for (kw, token) in keywords {
        if ident == kw {
            let mut tokens = tokenize(&src[(kw.len())..]);
            tokens.push_front(token);
            return tokens;
        }
    }

    let mut tokens = tokenize(&src[(ident.len())..]);
    tokens.push_front(Token::Ident(ident));
    tokens
}
