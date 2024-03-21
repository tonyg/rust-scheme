use std::iter::Peekable;
use itertools::Itertools;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Sexp<T> {
    Atom(T),
    List(Vec<Sexp<T>>),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Literal {
    Num(i64),
    Sym(String),
}

pub type InputSexp = Sexp<Literal>;

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

pub fn read_literal_atom<I: Iterator<Item = char>>(cs: &mut Peekable<I>) -> Option<Literal> {
    skip_whitespace(cs);
    match cs.peek() {
        Some(&ch) =>
            if ch.is_digit(10) {
                Some(Literal::Num(
                    cs.peeking_take_while(|ch| ch.is_digit(10))
                        .collect::<String>()
                        .parse()
                        .unwrap()))
            } else if ch.is_alphabetic() | is_sym_punctuation(ch) {
                Some(Literal::Sym(
                    cs.peeking_take_while(|ch| ch.is_alphanumeric() | is_sym_punctuation(*ch))
                        .collect::<String>()))
            } else {
                None
            },
        None => None,
    }
}

pub fn read_sexp<I: Iterator<Item = char>>(cs: &mut Peekable<I>) -> Result<InputSexp, String> {
    skip_whitespace(cs);
    match cs.peek() {
        Some(&'(') => {
            cs.next();
            let mut vs = Vec::new();
            loop {
                skip_whitespace(cs);
                if cs.peek() == Some(&')') {
                    cs.next();
                    return Ok(Sexp::List(vs));
                } else {
                    let v = read_sexp(cs)?;
                    vs.push(v);
                }
            }
        }
        _ =>
            read_literal_atom(cs).map_or(
                Err("Expected List or Atom".into()),
                |a| Ok(Sexp::Atom(a))),
    }
}

pub fn read_one_sexp(s: &str) -> Result<InputSexp, String> {
    read_sexp(&mut s.chars().peekable())
}

///////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod tests {
    use super::*;
    use Literal::*;
    use Sexp::*;

    #[test]
    fn read_little_numbers() {
        assert_eq!(Num(0), read_literal_atom(&mut "0".chars().peekable()).unwrap());
        assert_eq!(Num(1), read_literal_atom(&mut "1".chars().peekable()).unwrap());
        assert_eq!(Num(2), read_literal_atom(&mut "2".chars().peekable()).unwrap());
        assert_eq!(Num(234), read_literal_atom(&mut "234".chars().peekable()).unwrap());
        assert_eq!(Num(234), read_literal_atom(&mut "234ab".chars().peekable()).unwrap());
    }

    #[test]
    fn read_little_symbols() {
        assert_eq!(Sym("a".into()), read_literal_atom(&mut "a".chars().peekable()).unwrap());
        assert_eq!(Sym("abc".into()), read_literal_atom(&mut "abc".chars().peekable()).unwrap());
        assert_eq!(Sym("a17".into()), read_literal_atom(&mut "a17".chars().peekable()).unwrap());
        assert_eq!(Sym("a17".into()), read_literal_atom(&mut "a17 bq".chars().peekable()).unwrap());
    }

    #[test]
    fn read_sequence() {
        let p = &mut "99a17 bq 999 x  ".chars().peekable();
        assert_eq!(Num(99), read_literal_atom(p).unwrap());
        assert_eq!(Sym("a17".into()), read_literal_atom(p).unwrap());
        assert_eq!(Sym("bq".into()), read_literal_atom(p).unwrap());
        assert_eq!(Num(999), read_literal_atom(p).unwrap());
        assert_eq!(Sym("x".into()), read_literal_atom(p).unwrap());
        assert_eq!(None, read_literal_atom(p));
    }

    #[test]
    fn read_atomic_sexp() {
        assert!(read_one_sexp("").is_err());
        assert_eq!(Atom(Num(0)), read_one_sexp("0").unwrap());
        assert_eq!(Atom(Sym("a".into())), read_one_sexp("a b").unwrap());
    }

    #[test]
    fn read_nonatomic_sexp() {
        assert_eq!(List(vec![]), read_one_sexp("()").unwrap());
        assert_eq!(List(vec![Atom(Sym("a".into())),
                             Atom(Sym("b".into()))]),
                   read_one_sexp("(a b)").unwrap());
        assert_eq!(List(vec![Atom(Sym("a".into())),
                             List(vec![Atom(Sym("b".into()))]),
                             Atom(Sym("c".into()))]),
                   read_one_sexp("(a (b) c)").unwrap());
    }
}
