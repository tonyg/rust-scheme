use super::sexp::Literal;
use super::sexp::Sexp;
use super::sexp::InputSexp;

use super::prim::lookup_primitive;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Instruction<EnvRef, Formals> {
    ILit(ProgramValue),
    IVar(EnvRef),
    IApp(Box<Instruction<EnvRef, Formals>>, Vec<Instruction<EnvRef, Formals>>),
    IClo(Vec<EnvRef>, Formals, Box<Instruction<EnvRef, Formals>>),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum ProgramAtom {
    Lit(Literal),
    Prim(usize),
    Clo(Vec<ProgramValue>, u32, Box<TargetCode>)
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum EnvIndex {
    Env(usize),
    Arg(usize),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Bytecode {
    OpLiteral, // indexIntoLiterals
    OpEnvRef, // indexIntoEnvironment
    OpArgRef, // indexIntoArguments
    OpFrame, // countOfArguments
    OpJump, // zero
    OpCall, // zero
    OpReturn, // zero

    OpClosure, // indexIntoLiterals
    // OpClosure indexIntoLiterals points at consecutive slots:
    //    [arity, codepointer, litvec, capturecount, cap0, ... capN]
}

pub type ProgramValue = Sexp<ProgramAtom>;
pub type SourceCode = Instruction<String, Vec<String>>;
pub type TargetCode = Instruction<EnvIndex, usize>;

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
        Instruction::ILit(_) => (),
        Instruction::IVar(ref n) =>
            if !bound.contains(n) {
                if !free.contains(n) { free.push(n.clone()) }
            }
        Instruction::IApp(ref ratorbox, ref rands) => {
            free_vars(free, bound, ratorbox);
            for rand in rands {
                free_vars(free, bound, rand);
            }
        }
        Instruction::IClo(ref captures, ref formals, ref bodybox) => {
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

pub fn parse(s: &InputSexp) -> Result<SourceCode, String> {
    match *s {
        Sexp::Atom(Literal::Num(n)) =>
            Ok(Instruction::ILit(Sexp::Atom(ProgramAtom::Lit(Literal::Num(n))))),
        Sexp::Atom(Literal::Sym(ref v)) =>
            Ok(Instruction::IVar(v.clone())),
        Sexp::List(ref elts) => {
            if elts.len() == 0 {
                Ok(Instruction::ILit(Sexp::List(vec![])))
            } else if (elts.len() >= 2) & (elts[0] == Sexp::Atom(Literal::Sym("lambda".into()))) {
                let mut args = parse_formals(&elts[1])?;
                let body = parse_seq(&elts[2..])?;
                let mut fv = Vec::new();
                free_vars(&mut fv, &mut args, &body);
                Ok(Instruction::IClo(fv, args, Box::new(body)))
            } else {
                let mut exprs = elts.iter().map(parse).collect::<Result<Vec<SourceCode>,_>>()?;
                let first = exprs.remove(0);
                Ok(Instruction::IApp(Box::new(first), exprs.into()))
            }
        }
    }
}

///////////////////////////////////////////////////////////////////////////

fn name_to_envindex(envvars: &[String], argvars: &[String], n: &str) -> Option<EnvIndex> {
    // Check argvars first, because they must shadow envvars. (As it
    // happens, it turns out this isn't important, because free_vars
    // already correctly avoids even making a shadowed environment
    // value available.)
    if let Some(i) = argvars.iter().position(|e| e == n) { return Some(EnvIndex::Arg(i)) }
    if let Some(i) = envvars.iter().position(|e| e == n) { return Some(EnvIndex::Env(i)) }
    None
}

pub fn compile(
    envvars: &[String],
    argvars: &[String],
    s: &SourceCode,
) -> Result<TargetCode, String> {
    match *s {
        Instruction::ILit(ref v) => Ok(Instruction::ILit(v.clone())),
        Instruction::IVar(ref n) =>
            match name_to_envindex(envvars, argvars, n) {
                Some(loc) => Ok(Instruction::IVar(loc)),
                None => // Primitive or unbound
                    match lookup_primitive(n) {
                        Some((i,_p)) => Ok(Instruction::ILit(Sexp::Atom(ProgramAtom::Prim(i)))),
                        None => Err("Unbound variable: ".to_owned() + n)
                    }
            }
        Instruction::IApp(ref ratorbox, ref rands) => {
            let newrator = compile(envvars, argvars, ratorbox)?;
            let newrands = rands.iter().map(|r| compile(envvars, argvars, r))
                .collect::<Result<Vec<TargetCode>,_>>()?;
            Ok(Instruction::IApp(Box::new(newrator), newrands))
        }
        Instruction::IClo(ref captures_and_prims, ref formals, ref bodybox) => {
            let captures = captures_and_prims.iter()
                .filter(|n| name_to_envindex(envvars, argvars, n).is_some())
                .map(|n| n.clone())
                .collect::<Vec<String>>();
            let newbody = compile(&captures, formals, bodybox)?;
            Ok(Instruction::IClo(
                captures.iter().map(|n| name_to_envindex(envvars, argvars, n)).flat_map(|o| o)
                    .collect::<Vec<EnvIndex>>(),
                formals.len(),
                Box::new(newbody)))
        }
    }
}

///////////////////////////////////////////////////////////////////////////

impl std::convert::From<Bytecode> for u8 {
    fn from(value: Bytecode) -> Self {
        value as u8
    }
}

impl std::convert::TryFrom<u8> for Bytecode {
    type Error = ();

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(Bytecode::OpLiteral),
            1 => Ok(Bytecode::OpEnvRef),
            2 => Ok(Bytecode::OpArgRef),
            3 => Ok(Bytecode::OpFrame),
            4 => Ok(Bytecode::OpJump),
            5 => Ok(Bytecode::OpCall),
            6 => Ok(Bytecode::OpReturn),
            7 => Ok(Bytecode::OpClosure),
            _ => Err(())
        }
    }
}

///////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod tests {
    use super::*;

    use ProgramAtom::*;
    use Instruction::*;
    use EnvIndex::*;

    use crate::sexp::read_one_sexp;
    use crate::sexp::Sexp::*;
    use crate::sexp::Literal::*;

    #[test]
    fn parse_simple() {
        let parsed = parse(&read_one_sexp("((lambda (a b) (+ a b)) 123 234)").unwrap()).unwrap();
        assert_eq!(IApp(Box::new(IClo(vec!["+".into()],
                                      vec!["a".into(), "b".into()],
                                      Box::new(IApp(Box::new(IVar("+".into())),
                                                    vec![IVar("a".into()), IVar("b".into())])))),
                        vec![ILit(Atom(Lit(Num(123)))),
                             ILit(Atom(Lit(Num(234))))]),
                   parsed);
        assert_eq!(IApp(Box::new(IClo(vec![],
                                      2,
                                      Box::new(IApp(Box::new(ILit(Atom(Prim(0)))),
                                                    vec![IVar(Arg(0)),
                                                         IVar(Arg(1))])))),
                        vec![ILit(Atom(Lit(Num(123)))), ILit(Atom(Lit(Num(234))))]),
                   compile(&vec![], &vec![], &parsed).unwrap());
    }

    #[test]
    fn check_arg_shadowing() {
        let parsed = parse(&read_one_sexp("(lambda (x) (lambda (x) x))").unwrap()).unwrap();
        assert_eq!(IClo(vec![], 1, Box::new(IClo(vec![], 1, Box::new(IVar(Arg(0)))))),
                   compile(&vec![], &vec![], &parsed).unwrap());
    }

    #[test]
    fn test_bytecode_range() {
        // Supposed to ensure that we have 8 or fewer opcodes!
        assert!(u8::from(Bytecode::OpClosure) < 8);
    }
}
