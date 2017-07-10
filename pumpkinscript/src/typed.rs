// Copyright (c) 2017, All Contributors (see CONTRIBUTORS file)
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
use super::Receivable;
use std::io::Cursor;

use std::convert::TryFrom;

pub type InOut = (Vec<Type>, Vec<Type>);

pub type Parameter = usize;
pub type Offset = isize;

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Binary,
    Closure(InOut),
    Named(String),
    Parametrized(Parameter),
    ParametrizedSpread(Parameter),
    ParametrizedSpreadSub(Parameter, Offset, Offset),
}

impl From<Vec<u8>> for Type {
    fn from(v: Vec<u8>) -> Self {
        Type::Named(String::from_utf8(v).unwrap())
    }
}

#[derive(Debug, PartialEq)]
pub enum Error {
    Unknown,
    MismatchedTypes { expected: Type, got: Type },
    MissingType(Type),
}

impl From<()> for Error {
    fn from(_: ()) -> Self {
        Error::Unknown
    }
}

pub trait Typer {
    fn get_type<C : AsRef<[u8]> + PartialEq>(&self, code: C) -> Result<InOut, Error>;
}

pub struct Instructions;

impl Typer for Instructions {
    fn get_type<C : AsRef<[u8]> + PartialEq>(&self, code: C) -> Result<InOut, Error> {
        if code.as_ref() == b"DUP" {
            return Ok((vec![Type::Parametrized(1)], vec![Type::Parametrized(1), Type::Parametrized(1)]));
        }
        if code.as_ref() == b"TRUE" {
            return Ok((vec![], vec![Type::Named(String::from("BOOL"))]));
        }
        if code.as_ref() == b"CONCAT" {
            return Ok((vec![Type::Parametrized(1), Type::Parametrized(2)], vec![Type::Binary]));
        }
        if code.as_ref() == b"UINT/ADD" {
            return Ok((vec![Type::Named(String::from("UINT")), Type::Named(String::from("UINT"))], vec![Type::Named(String::from("UINT"))]));
        }
        if code.as_ref() == b"EVAL" {
            return Ok((vec![Type::ParametrizedSpread(1), Type::Closure((vec![Type::ParametrizedSpread(1)], vec![Type::ParametrizedSpread(2)]))],
                       vec![Type::ParametrizedSpread(2)]));
        }
        if code.as_ref() == b"DOWHILE" {
            return Ok((vec![Type::Closure((vec![], vec![Type::Named(String::from("BOOL"))]))],
                       vec![]));
        }
        Err(Error::Unknown)
    }
}

pub struct TypedPumpkinScript;

use std::collections::{BTreeMap, VecDeque};

trait Unify {
    type Effect;
    type Error;
    fn unify(&self, other: &Self) -> Result<Self::Effect, Self::Error>;
}

struct Renumbering<T>(usize, T);

impl<T> ::std::fmt::Debug for Renumbering<T> where T : ::std::fmt::Debug {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        f.debug_struct("Renumbering").field("index", &self.0).field("T", &self.1).finish()
    }
}

impl Unify for Type {
    type Effect = Vec<Renumbering<Vec<Type>>>;
    type Error = Error;

    fn unify(&self, other: &Self) -> Result<Self::Effect, Self::Error> {
        let mut effects = vec![];
        match (self, other) {
            (&Type::Parametrized(c_), &Type::Parametrized(c)) => {
                // if instruction's parametrized type is also
                // parametrized in this typing
                effects.push(Renumbering(c, vec![Type::Parametrized(c_)]));
            },
            (t1, &Type::Parametrized(c)) => {
                // if the instruction's type is parametrized but
                // there's a matching concrete type already
                effects.push(Renumbering(c, vec![t1.clone()]));
            },
            (ref t1, ref t2) if t1 == t2 => {
                // do nothing if the types are fully equal
            },
            (&Type::Closure((ref cin_, ref cout_)), &Type::Closure((ref cin, ref cout))) => {
                let mut effects_i = cin_.unify(cin)?;
                let mut effects_o = cout_.unify(cout)?;
                effects.append(&mut effects_i);
                effects.append(&mut effects_o);
            },
            (t1, t2) => {
                // type mismatch
                return Err(Error::MismatchedTypes {
                    expected: t2.clone(),
                    got: t1.clone(),
                })
            },
        }
        Ok(effects)
    }
}

impl Unify for Vec<Type> {
    type Effect = Vec<Renumbering<Vec<Type>>>;
    type Error = Error;

    fn unify(&self, other: &Self) -> Result<Self::Effect, Self::Error> {
        let mut effects = vec![];
        let mut iter = self.iter().peekable();
        let mut iter_other = other.iter().peekable();
        loop {
            let i = iter_other.next();
            let p = iter_other.peek();
            match i {
                Some(&Type::ParametrizedSpread(n)) => {
                    let mut renumbering = vec![];
                    loop {
                        match iter.next() {
                            None => {
                                effects.push(Renumbering(n, renumbering));
                                break;
                            },
                            Some(v) => {
                                match p {
                                    Some(pv) if pv == &v => {
                                        // end of the spread
                                        effects.push(Renumbering(n, renumbering));
                                        break;
                                    },
                                    _ => renumbering.push(v.clone()),
                                }
                            }
                        }
                    }
                },
                Some(v) => {
                    match iter.next() {
                        None => return Err(Error::MissingType(v.clone())),
                        Some(v_) => {
                            for Renumbering(n, r) in v_.unify(v)? {
                                effects.push(Renumbering(n, r));
                            }
                        }
                    }
                },
                None => break,
            }
        }
        Ok(effects)
    }
}

impl Typer for TypedPumpkinScript {

    fn get_type<C : AsRef<[u8]> + PartialEq>(&self, code: C) -> Result<InOut, Error> {
        let mut ctr = 0 as usize;
        let mut input = vec![];
        let mut output = vec![];
        let mut cur = Cursor::new(code.as_ref());
        let mut receivables = VecDeque::new();
        loop {
            // end of data
            if cur.position() as usize == cur.get_ref().len() {
                return Ok((input, output))
            }
            let receivable = Receivable::try_from(&mut cur)?;
            match receivable {
                Receivable::Data(_) => output.push(Type::Binary),
                // casting
                Receivable::Instruction(ref s) if s == "AS" => {
                    match receivables.back() {
                        None => return Err(Error::Unknown),
                        Some(&Receivable::Instruction(_)) => return Err(Error::Unknown),
                        Some(&Receivable::Data(ref t)) => {
                            let _ = output.pop().unwrap();
                            let _ = output.pop().unwrap();
                            if t == b"CLOSURE" {
                                let typ = TypedPumpkinScript.get_type(&receivables[receivables.len() - 2])?;
                                output.push(Type::Closure(typ));
                            } else {
                                output.push(t.clone().into());
                            }
                        },
                    }
                },
                Receivable::Instruction(ref i) => {
                    let (mut input_, mut output_) = Instructions.get_type(i)?;
                    let mut renumbering = BTreeMap::new();
                    loop {
                        match input_.pop() {
                            None => break,
                            Some(inp) => {
                                    match output.pop() {
                                        Some(t) => {
                                            for effect in t.unify(&inp)? {
                                                renumbering.insert(effect.0, effect.1);
                                            }
                                        },
                                        None => {
                                            match inp {
                                                Type::Parametrized(c) => {
                                                    ctr += 1;
                                                    match renumbering.get(&c) {
                                                        None => input.push(Type::Parametrized(ctr)),
                                                        Some(ref types) => for typ in types.iter() {
                                                            input.push(typ.clone());
                                                        },
                                                    }
                                                    renumbering.insert(c, vec![Type::Parametrized(ctr)]);
                                                },
                                                Type::ParametrizedSpread(c) => {
                                                    ctr += 1;
                                                    match renumbering.get(&c) {
                                                        None => input.push(Type::ParametrizedSpread(ctr)),
                                                        Some(ref types) => for typ in types.iter() {
                                                            input.push(typ.clone());
                                                        },
                                                    }
                                                    renumbering.insert(c, vec![Type::ParametrizedSpread(ctr)]);
                                                },
                                                other => input.push(other),
                                            }
                                        },
                                }
                            }
                        }
                    }
                    for o in output_.drain(..) {
                        match o {
                            Type::Parametrized(c) =>
                                output.append(&mut renumbering.get_mut(&c).unwrap().clone()),
                            Type::ParametrizedSpread(c) =>
                                output.append(&mut renumbering.get_mut(&c).unwrap().clone()),
                            other => output.push(other),
                        }
                    }
                },
            }
            receivables.push_back(receivable);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use {parse_with_config, ParseConfigBuilder, Program, ParseError};

    pub fn parse_typed(script: &str) -> Result<Program, ParseError> {
        let config = ParseConfigBuilder::default().type_literals(true).build().unwrap();
        parse_with_config(script, config)
    }

    #[test]
    fn single_instruction_param() {
        let result = TypedPumpkinScript.get_type(parse_typed("DUP").unwrap()).unwrap();
        assert_eq!(result, (vec![Type::Parametrized(1)], vec![Type::Parametrized(1), Type::Parametrized(1)]));
    }

    #[test]
    fn type_inference() {
        let result = TypedPumpkinScript.get_type(parse_typed("\"test\" DUP").unwrap()).unwrap();
        assert_eq!(result, (vec![], vec![Type::Named(String::from("STRING")), Type::Named(String::from("STRING"))]));
        let result = TypedPumpkinScript.get_type(parse_typed("\"test\" 1 CONCAT").unwrap()).unwrap();
        assert_eq!(result, (vec![], vec![Type::Binary]));
    }

    #[test]
    fn mismatch() {
        let result = TypedPumpkinScript.get_type(parse_typed("\"test\" DUP 1 UINT/ADD").unwrap()).unwrap_err();
        assert_eq!(result, Error::MismatchedTypes {expected: Type::Named(String::from("UINT")),
                                                   got: Type::Named(String::from("STRING"))});
    }


    #[test]
    fn closure() {
        let result = TypedPumpkinScript.get_type(parse_typed("[DUP]").unwrap()).unwrap();
        assert_eq!(result, (vec![], vec![Type::Closure((vec![Type::Parametrized(1)],
                                                        vec![Type::Parametrized(1), Type::Parametrized(1)]))]));
        let result = TypedPumpkinScript.get_type(parse_typed("[TRUE] DOWHILE").unwrap()).unwrap();
        assert_eq!(result, (vec![], vec![]));
        let result = TypedPumpkinScript.get_type(parse_typed("[DUP] EVAL").unwrap()).unwrap();
        assert_eq!(result, (vec![Type::Parametrized(1)], vec![Type::Parametrized(1), Type::Parametrized(1)]));
    }

}