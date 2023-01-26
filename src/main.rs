#![feature(box_patterns)]

mod parse;
mod tokenize;

use std::collections::{HashMap, LinkedList};
use std::fmt::Debug;

use crate::parse::*;
use crate::tokenize::*;

enum ProjectionError<'a> {
    NameNotFound(&'a str),
}

impl<'a> Debug for ProjectionError<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NameNotFound(name) => {
                write!(f, "[projection] `{}` is not found in the pattern.", name)
            }
        }
    }
}

fn projection<'a>(
    pat: &Pattern,
    name: &'a str,
    value: Value,
) -> Result<Value, ProjectionError<'a>> {
    match pat {
        Pattern::Var(var) if var == name => Ok(value),
        Pattern::Pair(a, _) if a.contains(name) => projection(a, name, value.first()),
        Pattern::Pair(_, b) if b.contains(name) => projection(b, name, value.second()),
        _ => Err(ProjectionError::NameNotFound(name)),
    }
}

#[derive(Debug, Clone, PartialEq)]
enum Value {
    Universe,
    UnitType,
    UnitElement,
    Lambda(Box<FunctionClosure>),
    Pi(Box<Self>, Box<FunctionClosure>),
    Sigma(Box<Self>, Box<FunctionClosure>),
    Pair(Box<Self>, Box<Self>),
    Construct(Constructor, Box<Value>),
    Fun(usize, Box<ChoiceClosure>),
    Sum(usize, Box<ChoiceClosure>),
    Neutral(Box<NeutralValue>),
}

impl Value {
    fn readback(&self, i: usize) -> Expression {
        let pat = Pattern::Var(format!("#{}", i));
        let gen = Value::Neutral(Box::new(NeutralValue::FreeVariable(format!("#{}", i), i)));
        match self {
            Self::Lambda(box f) => {
                Expression::Lambda(pat, Box::new(f.instantiate(&gen).readback(i + 1)))
            }
            Self::Pair(a, b) => Expression::Pair(Box::new(a.readback(i)), Box::new(b.readback(i))),
            Self::UnitElement => Expression::UnitElement,
            Self::Construct(con, v) => Expression::Construct(con.clone(), Box::new(v.readback(i))),
            Self::Fun(index, box ChoiceClosure(_, env))
            | Self::Sum(index, box ChoiceClosure(_, env)) => env
                .readback(i)
                .into_iter()
                .rev()
                .fold(Expression::Variable(format!("{}", index)), |acc, e| {
                    Expression::Apply(Box::new(e), Box::new(acc))
                }),
            Self::Universe => Expression::Universe,
            Self::UnitType => Expression::UnitType,
            Self::Pi(t, g) => Expression::Pi(
                pat,
                Box::new(t.readback(i)),
                Box::new(g.instantiate(&gen).readback(i + 1)),
            ),
            Self::Sigma(t, g) => Expression::Sigma(
                pat,
                Box::new(t.readback(i)),
                Box::new(g.instantiate(&gen).readback(i + 1)),
            ),
            Self::Neutral(k) => k.readback(i),
        }
    }

    fn apply(&self, arg: Self) -> Self {
        match (self, arg) {
            (Self::Lambda(f), v) => f.instantiate(&v),
            (Self::Fun(_, box ChoiceClosure(choices, env)), Self::Construct(choice, box v)) => {
                env.evaluate(choices.get(&choice)).apply(v)
            }
            (Self::Fun(_, box cc), Value::Neutral(nv)) => {
                Self::Neutral(Box::new(NeutralValue::Choice(cc.clone(), nv)))
            }
            (Self::Neutral(nv), v) => Self::Neutral(Box::new(NeutralValue::Apply(nv.clone(), v))),
            (a, b) => panic!("[apply] {:?} {:?}", a, b),
        }
    }

    fn first(&self) -> Self {
        match self {
            Self::Pair(box fst, _) => fst.clone(),
            Self::Neutral(nv) => Self::Neutral(Box::new(NeutralValue::First(nv.clone()))),
            v => panic!("[first] {:?}", v),
        }
    }

    fn second(&self) -> Self {
        match self {
            Self::Pair(_, box snd) => snd.clone(),
            Self::Neutral(nv) => Self::Neutral(Box::new(NeutralValue::Second(nv.clone()))),
            v => panic!("[second] {:?}", v),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
enum NeutralValue {
    FreeVariable(String, usize),
    Apply(Box<Self>, Value),
    First(Box<Self>),
    Second(Box<Self>),
    Choice(ChoiceClosure, Box<Self>),
}

impl NeutralValue {
    fn readback(&self, i: usize) -> Expression {
        match self {
            Self::FreeVariable(name, j) => Expression::Variable(format!("#{}{}", name, j)),
            Self::Apply(k, m) => {
                Expression::Apply(Box::new(k.readback(i)), Box::new(m.readback(i)))
            }
            Self::First(k) => Expression::First(Box::new(k.readback(i))),
            Self::Second(k) => Expression::Second(Box::new(k.readback(i))),
            Self::Choice(ChoiceClosure(_, env), k) => {
                let exprs = env
                    .readback(i)
                    .into_iter()
                    .rev()
                    .fold(Expression::Variable(format!("#{}", i)), |acc, e| {
                        Expression::Apply(Box::new(e), Box::new(acc))
                    });
                Expression::Apply(Box::new(exprs), Box::new(k.readback(i)))
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
enum FunctionClosure {
    Closure(Pattern, Expression, Environment),
    Choice(Box<Self>, Constructor),
}

impl FunctionClosure {
    fn instantiate(&self, value: &Value) -> Value {
        match self {
            FunctionClosure::Closure(pat, expr, env) => env
                .push_variable(pat.clone(), value.clone())
                .evaluate(&expr),
            FunctionClosure::Choice(f, con) => {
                let arg = Value::Construct(con.clone(), Box::new(value.clone()));
                f.instantiate(&arg)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct ChoiceClosure(Choices, Environment);

#[derive(Debug, Clone, PartialEq)]
enum Environment {
    Empty,
    Variable(Box<Self>, Pattern, Value),
    Declaration(Box<Self>, Declaration),
}

impl Environment {
    fn push_variable(&self, pat: Pattern, value: Value) -> Self {
        Self::Variable(Box::new(self.clone()), pat, value)
    }

    fn push_declaration(&self, decl: Declaration) -> Self {
        Self::Declaration(Box::new(self.clone()), decl)
    }

    fn get(&self, name: &str) -> Value {
        match self {
            Self::Empty => panic!("[Environment::get] {} is not found", name),
            Self::Variable(rest, pat, v) => {
                if pat.contains(name) {
                    projection(pat, name, v.clone()).unwrap()
                } else {
                    rest.get(name)
                }
            }
            Self::Declaration(env, Declaration::Define(pat, _, e)) => {
                if pat.contains(name) {
                    projection(pat, name, env.evaluate(e)).unwrap()
                } else {
                    env.get(name)
                }
            }
            Self::Declaration(env, Declaration::DefineRec(pat, _, e)) => {
                if pat.contains(name) {
                    projection(pat, name, self.evaluate(e)).unwrap()
                } else {
                    env.get(name)
                }
            }
        }
    }

    fn evaluate(&self, expr: &Expression) -> Value {
        match expr {
            Expression::Universe => Value::Universe,
            Expression::UnitType => Value::UnitType,
            Expression::UnitElement => Value::UnitElement,
            Expression::Lambda(pat, box expr) => Value::Lambda(Box::new(FunctionClosure::Closure(
                pat.clone(),
                expr.clone(),
                self.clone(),
            ))),
            Expression::Variable(var) => self.get(&var),
            Expression::Apply(box f, box a) => self.evaluate(f).apply(self.evaluate(a)),
            Expression::Pi(pat, box a, box b) => Value::Pi(
                Box::new(self.evaluate(a)),
                Box::new(FunctionClosure::Closure(
                    pat.clone(),
                    b.clone(),
                    self.clone(),
                )),
            ),
            Expression::Pair(box a, box b) => {
                Value::Pair(Box::new(self.evaluate(a)), Box::new(self.evaluate(b)))
            }
            Expression::First(box e) => self.evaluate(e).first(),
            Expression::Second(box e) => self.evaluate(e).second(),
            Expression::Sigma(pat, box a, box b) => Value::Sigma(
                Box::new(self.evaluate(a)),
                Box::new(FunctionClosure::Closure(
                    pat.clone(),
                    b.clone(),
                    self.clone(),
                )),
            ),
            Expression::Construct(con, box v) => {
                Value::Construct(con.clone(), Box::new(self.evaluate(v)))
            }
            Expression::Fun(index, choices) => Value::Fun(
                *index,
                Box::new(ChoiceClosure(choices.clone(), self.clone())),
            ),
            Expression::Sum(index, choices) => Value::Sum(
                *index,
                Box::new(ChoiceClosure(choices.clone(), self.clone())),
            ),
            Expression::Declaration(box decl, box expr) => {
                self.push_declaration(decl.clone()).evaluate(expr)
            }
        }
    }

    fn readback(&self, i: usize) -> LinkedList<Expression> {
        match self {
            Self::Empty => LinkedList::new(),
            Self::Variable(rest, _, v) => {
                let mut rest = rest.readback(i);
                rest.push_back(v.readback(i));
                rest
            }
            Self::Declaration(rest, _) => rest.readback(i),
        }
    }

    fn l(&self) -> usize {
        match self {
            Environment::Empty => 0,
            Environment::Variable(rest, _, _) => rest.l() + 1,
            Environment::Declaration(rest, _) => rest.l(),
        }
    }

    fn free_variable(&self) -> Value {
        let i = self.l();
        Value::Neutral(Box::new(NeutralValue::FreeVariable(format!("#{}", i), i)))
    }
}

#[derive(Debug, Clone)]
struct TypeContext(HashMap<String, Value>);

impl TypeContext {
    fn new() -> Self {
        Self(HashMap::new())
    }

    fn get(&self, name: &str) -> Option<Value> {
        let Self(entries) = self;
        entries.get(name).cloned()
    }

    fn push(&self, pat: Pattern, ty: Value, value: Value) -> Option<Self> {
        match (pat, ty) {
            (Pattern::Unit, _) => Some(self.clone()),
            (Pattern::Var(var), ty) => {
                let Self(mut entries) = self.clone();
                entries.insert(var, ty);
                Some(Self(entries))
            }
            (Pattern::Pair(box a, box b), Value::Sigma(box t, box g)) => self
                .push(a, t, value.first())?
                .push(b, g.instantiate(&value.first()), value.second()),
            _ => None,
        }
    }
}

enum TypeCheckError {
    CannotInfer,
    NotFunction,
    NotTuple,
    InvalidDefinition,
    VariableNotFound(String),
    MismatchedType(Expression, Value),
}

impl Debug for TypeCheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::CannotInfer => write!(f, "CannotInfer"),
            Self::NotFunction => write!(f, "NotFunction"),
            Self::NotTuple => write!(f, "NotTuple"),
            Self::InvalidDefinition => write!(f, "InvalidDefinition"),
            Self::VariableNotFound(arg0) => f.debug_tuple("VariableNotFound").field(arg0).finish(),
            Self::MismatchedType(arg0, arg1) => f
                .debug_tuple("UnexpectedType")
                .field(arg0)
                .field(arg1)
                .finish(),
        }
    }
}

struct TypeCheck {
    environment: Environment,
    type_context: TypeContext,
}

impl TypeCheck {
    fn new() -> Self {
        Self {
            environment: Environment::Empty,
            type_context: TypeContext::new(),
        }
    }

    fn dummy(&self) -> Value {
        self.environment.free_variable()
    }

    fn push_variable(&self, pat: Pattern, ty: Value, value: Value) -> Result<Self, TypeCheckError> {
        Ok(Self {
            environment: self.environment.push_variable(pat.clone(), value.clone()),
            type_context: self
                .type_context
                .push(pat.clone(), ty.clone(), value.clone())
                .ok_or(TypeCheckError::InvalidDefinition)?,
        })
    }

    fn push_declaration(&self, decl: &Declaration) -> Result<Self, TypeCheckError> {
        self.check_declaration(decl).map(|type_context| Self {
            environment: self.environment.push_declaration(decl.clone()),
            type_context,
        })
    }

    fn check_declaration(&self, decl: &Declaration) -> Result<TypeContext, TypeCheckError> {
        match decl {
            Declaration::Define(p, a, e) => {
                self.is_type(a)?;

                let t = self.environment.evaluate(a);
                self.is(e, &t)?;

                let m = self.environment.evaluate(e);
                self.type_context
                    .push(p.clone(), t, m)
                    .ok_or(TypeCheckError::InvalidDefinition)
            }
            Declaration::DefineRec(p, a, e) => {
                self.is_type(a)?;

                let t = self.environment.evaluate(a);
                self.push_variable(p.clone(), t.clone(), self.dummy())?
                    .is(e, &t)?;

                let v = self.environment.push_declaration(decl.clone()).evaluate(e);
                self.type_context
                    .push(p.clone(), t, v)
                    .ok_or(TypeCheckError::InvalidDefinition)
            }
        }
    }

    fn infer_type(&self, expr: &Expression) -> Result<Value, TypeCheckError> {
        match expr {
            Expression::Variable(x) => self
                .type_context
                .get(&x)
                .ok_or(TypeCheckError::VariableNotFound(x.clone())),
            Expression::Apply(box m, box n) => {
                let Value::Pi(t, g) = self.infer_type(m)? else {
                    return Err(TypeCheckError::NotFunction);
                };

                self.is(n, &t)?;

                Ok(g.instantiate(&self.environment.evaluate(n)))
            }
            Expression::First(m) => {
                let Value::Sigma(t, _) = self.infer_type(m)? else {
                    return Err(TypeCheckError::NotTuple);
                };
                Ok(*t)
            }
            Expression::Second(box m) => {
                let Value::Sigma(_, box g) = self.infer_type(m)? else {
                    return Err(TypeCheckError::NotTuple);
                };
                Ok(g.instantiate(&self.environment.evaluate(m).first()))
            }
            _ => Err(TypeCheckError::CannotInfer),
        }
    }

    fn is_type(&self, expr: &Expression) -> Result<(), TypeCheckError> {
        match expr {
            Expression::Universe => Ok(()),
            Expression::UnitType => Ok(()),
            Expression::Pi(pat, box a, box b) | Expression::Sigma(pat, box a, box b) => {
                self.is_type(a)?;
                self.push_variable(pat.clone(), self.environment.evaluate(a), self.dummy())?
                    .is_type(b)
            }
            other => self.is(other, &Value::Universe),
        }
    }

    fn is(&self, expr: &Expression, ty: &Value) -> Result<(), TypeCheckError> {
        match (expr, ty) {
            (Expression::Lambda(p, box e), Value::Pi(box t, box g)) => {
                let gen = self.dummy();
                self.push_variable(p.clone(), t.clone(), gen.clone())?
                    .is(e, &g.instantiate(&gen))
            }
            (Expression::Pair(box m, box n), Value::Sigma(box t, box g)) => {
                self.is(m, t)?;
                self.is(n, &g.instantiate(&self.environment.evaluate(m)))
            }
            (
                Expression::Construct(con, box m),
                Value::Sum(_, box ChoiceClosure(choices, env2)),
            ) => {
                let a = choices.get(con);
                self.is(m, &env2.evaluate(a))
            }
            (
                Expression::Fun(_, choices),
                Value::Pi(box Value::Sum(_, box ChoiceClosure(choices2, env2)), g),
            ) => {
                if choices.is_same_struct(choices2) {
                    for ((c, e), (_, a)) in choices.iter().zip(choices2.iter()) {
                        self.is(
                            e,
                            &Value::Pi(
                                Box::new(env2.evaluate(a)),
                                Box::new(FunctionClosure::Choice(g.clone(), c.clone())),
                            ),
                        )?;
                    }
                    Ok(())
                } else {
                    panic!("case")
                }
            }
            (Expression::Declaration(box decl, box e), ty) => {
                self.push_declaration(decl)?.is(e, ty)
            }
            (Expression::UnitElement, Value::UnitType) => Ok(()),
            (Expression::UnitType, Value::Universe) => Ok(()),
            (Expression::Pi(p, box a, box b), Value::Universe)
            | (Expression::Sigma(p, box a, box b), Value::Universe) => {
                self.is(a, &Value::Universe)?;
                self.push_variable(p.clone(), self.environment.evaluate(a), self.dummy())?
                    .is(b, &Value::Universe)
            }
            (Expression::Sum(_, choices), Value::Universe) => {
                for (_, a) in choices.iter() {
                    self.is(a, &Value::Universe)?;
                }
                Ok(())
            }
            (m, ty_expected) => {
                let ty_inferred = self.infer_type(m)?;

                let l = self.environment.l();
                if ty_expected.readback(l) == ty_inferred.readback(l) {
                    Ok(())
                } else {
                    Err(TypeCheckError::MismatchedType(
                        m.clone(),
                        ty_expected.clone(),
                    ))
                }
            }
        }
    }
}

fn main() {
    let test = r#"
        let bool: U = Sum (True | False);

        let true_ty: U = Sum (TrueTy);
        let false_ty: U = Sum (FalseTy);
        let bool2ty: bool -> U = fun (True => true_ty | False => false_ty);
        let bool2ty_v: Π b: bool. bool2ty b = fun (True => TrueTy | False => FalseTy);

        let function_ty: bool → U = fun (True => bool | False => 1);
        let function: Π b: bool. function_ty b = fun (True => True | False => 0);

        let rec nat: U = Sum (Zero | Succ nat);

        let rec list: U -> U = λt.Sum (Nil | Cons t × list t);
        let rec length: Π t: U. list t -> nat = λt.fun (Nil => Zero | Cons _, l => Succ (length t l));


        let rec nat_eq: nat -> nat -> bool = fun (
            Zero => fun (
                Zero => True
                | Succ _ => False
            )
            | Succ n' => fun (
                Zero => False
                | Succ m' => nat_eq n' m'
            )
        );

        let rec nat_eq_ty: Π n:nat. Π m:nat. bool2ty (nat_eq n m) = λn. λm. bool2ty_v (nat_eq n m);

        let three: nat = Succ (Succ (Succ Zero));
        let li: list 1 = Cons (0, Cons (0, Cons (0, Nil)));

        let _: true_ty = nat_eq_ty three (length 1 li);
    "#;

    let tokens = tokenize(test);
    let tokens = tokens.into_iter().collect::<Vec<_>>();
    let parsed = parse(&tokens);
    println!("{:?}", parsed);

    let (parsed, rest) = parsed.unwrap();
    assert!(rest.is_empty());

    TypeCheck::new().is(&parsed, &Value::UnitType).unwrap();
    println!("typed.");
}
