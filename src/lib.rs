extern crate itertools;

use std::iter::Peekable;
use itertools::Itertools;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
enum Sexp<T> {
    Atom(T),
    List(Vec<Sexp<T>>),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
enum Literal {
    Num(i64),
    Sym(String),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
enum Instruction<EnvRef, Formals> {
    Lit(InputSexp),
    Var(EnvRef),
    App(Box<Instruction<EnvRef, Formals>>, Vec<Instruction<EnvRef, Formals>>),
    Clo(Vec<EnvRef>, Formals, Box<Instruction<EnvRef, Formals>>),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
enum ProgramAtom {
    Lit(Literal),
    Prim(usize),
    Clo(Vec<ProgramValue>, u32, TargetCode)
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
enum EnvIndex {
    Env(usize),
    Arg(usize),
}

type InputSexp = Sexp<Literal>;
type ProgramValue = Sexp<ProgramAtom>;
type SourceCode = Instruction<String, Vec<String>>;
type TargetCode = Instruction<EnvIndex, usize>;

///////////////////////////////////////////////////////////////////////////

// impl<T> Sexp<T> {
//     pub fn is_atom(&self) -> bool {
//         match *self {
//             Sexp::Atom(_) => true,
//             Sexp::List(_) => false
//         }
//     }

//     pub fn is_list(&self) -> bool {
//         match *self {
//             Sexp::Atom(_) => false,
//             Sexp::List(_) => true
//         }
//     }
// }

///////////////////////////////////////////////////////////////////////////

fn skip_whitespace<I: Iterator<Item = char>>(cs: &mut Peekable<I>) -> () {
    while cs.peek().map(|c| c.is_whitespace()) == Some(true) {
        cs.next();
    }
}

fn is_sym_punctuation(c: char) -> bool {
    match c {
        '+' => true,
        _ => false
    }
}

fn read_literal_atom<I: Iterator<Item = char>>(cs: &mut Peekable<I>) -> Option<Literal> {
    use Literal::*;
    skip_whitespace(cs);
    match cs.peek() {
        Some(&ch) =>
            if ch.is_digit(10) {
                Some(Num(cs.peeking_take_while(|ch| ch.is_digit(10))
                         .collect::<String>()
                         .parse()
                         .unwrap()))
            } else if ch.is_alphabetic() | is_sym_punctuation(ch) {
                Some(Sym(cs.peeking_take_while(|ch| ch.is_alphanumeric() | is_sym_punctuation(*ch))
                         .collect::<String>()))
            } else {
                None
            },
        None => None,
    }
}

fn read_sexp<I: Iterator<Item = char>>(cs: &mut Peekable<I>) -> Result<InputSexp, String> {
    use Sexp::*;
    skip_whitespace(cs);
    match cs.peek() {
        Some(&'(') => {
            cs.next();
            let mut vs = Vec::new();
            loop {
                skip_whitespace(cs);
                if cs.peek() == Some(&')') {
                    cs.next();
                    return Ok(List(vs));
                } else {
                    let v = read_sexp(cs)?;
                    vs.push(v);
                }
            }
        }
        _ => read_literal_atom(cs).map_or(Err("Expected List or Atom".into()), |a| Ok(Atom(a))),
    }
}

///////////////////////////////////////////////////////////////////////////

fn parse_formals(s: &InputSexp) -> Result<Vec<String>, String> {
    match *s {
        Sexp::List(ref elts) => {
            let mut names = Vec::new();
            for f in elts {
                match *f {
                    Sexp::Atom(Literal::Sym(ref name)) => names.push(name.clone()),
                    _ => return Err("Each formal must be a symbol".into())
                }
            }
            Ok(names)
        }
        _ => Err("Formals must be a list".into())
    }
}

fn parse_seq(s: &[InputSexp]) -> Result<SourceCode, String> {
    if s.len() == 0 {
        Err("Expected expression in sequence".into())
    } else if s.len() == 1 {
        parse(&s[0])
    } else {
        Err("begin with many exprs is unimplemented".into())
    }
}

fn free_vars(free: &mut Vec<String>, bound: &mut Vec<String>, expr: &SourceCode) -> () {
    match *expr {
        Instruction::Lit(_) => (),
        Instruction::Var(ref n) =>
            if !bound.contains(n) {
                if !free.contains(n) { free.push(n.clone()) }
            }
        Instruction::App(ref ratorbox, ref rands) => {
            free_vars(free, bound, ratorbox);
            for rand in rands {
                free_vars(free, bound, rand);
            }
        }
        Instruction::Clo(ref captures, ref formals, ref bodybox) => {
            for n in captures {
                if !free.contains(n) { free.push(n.clone()) }
            }
            let orig_bound_len = bound.len();
            bound.extend(formals.iter().cloned());
            free_vars(free, bound, bodybox);
            bound.truncate(orig_bound_len);
        }
    }
}

fn parse(s: &InputSexp) -> Result<SourceCode, String> {
    use Sexp::*;
    use Instruction::*;
    use Literal::*;
    match *s {
        Atom(Num(_)) => Ok(Lit(s.clone())),
        Atom(Sym(ref v)) => Ok(Var(v.clone())),
        List(ref elts) => {
            if elts.len() == 0 {
                Ok(Lit(List(vec![])))
            } else if (elts.len() >= 2) & (elts[0] == Atom(Sym("lambda".into()))) {
                let mut args = parse_formals(&elts[1])?;
                let body = parse_seq(&elts[2..])?;
                let mut fv = Vec::new();
                free_vars(&mut fv, &mut args, &body);
                Ok(Clo(fv, args, Box::new(body)))
            } else {
                let mut exprs = elts.iter().map(parse).collect::<Result<Vec<SourceCode>,_>>()?;
                let first = exprs.remove(0);
                Ok(App(Box::new(first), exprs.into()))
            }
        }
    }
}

///////////////////////////////////////////////////////////////////////////

fn name_to_envindex(envvars: &[String], argvars: &[String], n: &str) -> Result<EnvIndex, String> {
    // Check argvars first, because they must shadow envvars. (As it
    // happens, it turns out this isn't important, because free_vars
    // already correctly avoids even making a shadowed environment
    // value available.)
    if let Some(i) = argvars.iter().position(|e| e == n) {
        return Ok(EnvIndex::Arg(i))
    }
    if let Some(i) = envvars.iter().position(|e| e == n) {
        return Ok(EnvIndex::Env(i))
    }
    Err("Unbound variable: ".to_owned() + n)
}

fn compile(envvars: &[String], argvars: &[String], s: &SourceCode) -> Result<TargetCode, String> {
    use Instruction::*;
    match *s {
        Lit(ref v) => Ok(Lit(v.clone())),
        Var(ref n) => Ok(Var(name_to_envindex(envvars, argvars, n)?)),
        App(ref ratorbox, ref rands) => {
            let newrator = compile(envvars, argvars, ratorbox)?;
            let newrands = rands.iter().map(|r| compile(envvars, argvars, r))
                .collect::<Result<Vec<TargetCode>,_>>()?;
            Ok(App(Box::new(newrator), newrands))
        }
        Clo(ref captures, ref formals, ref bodybox) => {
            let newbody = compile(captures, formals, bodybox)?;
            Ok(Clo(captures.iter().map(|n| name_to_envindex(envvars, argvars, n))
                   .collect::<Result<Vec<EnvIndex>,_>>()?,
                   formals.len(),
                   Box::new(newbody)))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn read_little_numbers() {
        assert_eq!(
            Literal::Num(0),
            read_literal_atom(&mut "0".chars().peekable()).unwrap()
        );
        assert_eq!(
            Literal::Num(1),
            read_literal_atom(&mut "1".chars().peekable()).unwrap()
        );
        assert_eq!(
            Literal::Num(2),
            read_literal_atom(&mut "2".chars().peekable()).unwrap()
        );
        assert_eq!(
            Literal::Num(234),
            read_literal_atom(&mut "234".chars().peekable()).unwrap()
        );
        assert_eq!(
            Literal::Num(234),
            read_literal_atom(&mut "234ab".chars().peekable()).unwrap()
        );
    }

    #[test]
    fn read_little_symbols() {
        assert_eq!(
            Literal::Sym("a".into()),
            read_literal_atom(&mut "a".chars().peekable()).unwrap()
        );
        assert_eq!(
            Literal::Sym("abc".into()),
            read_literal_atom(&mut "abc".chars().peekable()).unwrap()
        );
        assert_eq!(
            Literal::Sym("a17".into()),
            read_literal_atom(&mut "a17".chars().peekable()).unwrap()
        );
        assert_eq!(
            Literal::Sym("a17".into()),
            read_literal_atom(&mut "a17 bq".chars().peekable()).unwrap()
        );
    }

    #[test]
    fn read_sequence() {
        let p = &mut "99a17 bq 999 x  ".chars().peekable();
        assert_eq!(Literal::Num(99), read_literal_atom(p).unwrap());
        assert_eq!(Literal::Sym("a17".into()), read_literal_atom(p).unwrap());
        assert_eq!(Literal::Sym("bq".into()), read_literal_atom(p).unwrap());
        assert_eq!(Literal::Num(999), read_literal_atom(p).unwrap());
        assert_eq!(Literal::Sym("x".into()), read_literal_atom(p).unwrap());
        assert_eq!(None, read_literal_atom(p));
    }

    fn read_one_sexp(s: &str) -> Result<InputSexp, String> {
        read_sexp(&mut s.chars().peekable())
    }

    #[test]
    fn read_atomic_sexp() {
        assert!(read_one_sexp("").is_err());
        assert_eq!(Sexp::Atom(Literal::Num(0)), read_one_sexp("0").unwrap());
        assert_eq!(Sexp::Atom(Literal::Sym("a".into())), read_one_sexp("a b").unwrap());
    }

    #[test]
    fn read_nonatomic_sexp() {
        assert_eq!(Sexp::List(vec![]), read_one_sexp("()").unwrap());
        assert_eq!(Sexp::List(vec![Sexp::Atom(Literal::Sym("a".into())),
                                   Sexp::Atom(Literal::Sym("b".into()))]),
                   read_one_sexp("(a b)").unwrap());
        assert_eq!(Sexp::List(vec![Sexp::Atom(Literal::Sym("a".into())),
                                   Sexp::List(vec![Sexp::Atom(Literal::Sym("b".into()))]),
                                   Sexp::Atom(Literal::Sym("c".into()))]),
                   read_one_sexp("(a (b) c)").unwrap());
    }

    #[test]
    fn parse_simple() {
        use Literal::*;
        use Sexp::*;
        use Instruction::*;
        let parsed = parse(&read_one_sexp("((lambda (a b) (+ a b)) 123 234)").unwrap()).unwrap();
        assert_eq!(App(Box::new(Clo(vec!["+".into()],
                                    vec!["a".into(), "b".into()],
                                    Box::new(App(Box::new(Var("+".into())),
                                                 vec![Var("a".into()), Var("b".into())])))),
                       vec![Lit(Atom(Num(123))),
                            Lit(Atom(Num(234)))]),
                   parsed);
        assert_eq!(App(Box::new(Clo(vec![EnvIndex::Env(1)],
                                    2,
                                    Box::new(App(Box::new(Var(EnvIndex::Env(0))),
                                                 vec![Var(EnvIndex::Arg(0)),
                                                      Var(EnvIndex::Arg(1))])))),
                       vec![Lit(Atom(Num(123))), Lit(Atom(Num(234)))]),
                   compile(&vec!["cons".into(), "+".into()], &vec![], &parsed).unwrap());
    }

    #[test]
    fn check_arg_shadowing() {
        use Literal::*;
        use Sexp::*;
        use Instruction::*;
        let parsed = parse(&read_one_sexp("(lambda (x) (lambda (x) x))").unwrap()).unwrap();
        assert_eq!(Clo(vec![], 1, Box::new(Clo(vec![], 1, Box::new(Var(EnvIndex::Arg(0)))))),
                   compile(&vec![], &vec![], &parsed).unwrap());
    }
}
