#![allow(dead_code)] // TODO: turn this off again

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
    ILit(ProgramValue),
    IVar(EnvRef),
    IApp(Box<Instruction<EnvRef, Formals>>, Vec<Instruction<EnvRef, Formals>>),
    IClo(Vec<EnvRef>, Formals, Box<Instruction<EnvRef, Formals>>),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
enum ProgramAtom {
    Lit(Literal),
    Prim(usize),
    Clo(Vec<ProgramValue>, u32, Box<TargetCode>)
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
enum EnvIndex {
    Env(usize),
    Arg(usize),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
enum Bytecode {
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

type InputSexp = Sexp<Literal>;
type ProgramValue = Sexp<ProgramAtom>;
type SourceCode = Instruction<String, Vec<String>>;
type TargetCode = Instruction<EnvIndex, usize>;

use Literal::*;
use Sexp::*;
use Instruction::*;
use ProgramAtom::*;
use EnvIndex::*;
use Bytecode::*;

///////////////////////////////////////////////////////////////////////////

// impl<T> Sexp<T> {
//     pub fn is_atom(&self) -> bool {
//         match *self {
//             Atom(_) => true,
//             List(_) => false
//         }
//     }

//     pub fn is_list(&self) -> bool {
//         match *self {
//             Atom(_) => false,
//             List(_) => true
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
        List(ref elts) => {
            let mut names = Vec::new();
            for f in elts {
                match *f {
                    Atom(Sym(ref name)) => names.push(name.clone()),
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
        ILit(_) => (),
        IVar(ref n) =>
            if !bound.contains(n) {
                if !free.contains(n) { free.push(n.clone()) }
            }
        IApp(ref ratorbox, ref rands) => {
            free_vars(free, bound, ratorbox);
            for rand in rands {
                free_vars(free, bound, rand);
            }
        }
        IClo(ref captures, ref formals, ref bodybox) => {
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
    match *s {
        Atom(Num(n)) => Ok(ILit(Atom(Lit(Num(n))))),
        Atom(Sym(ref v)) => Ok(IVar(v.clone())),
        List(ref elts) => {
            if elts.len() == 0 {
                Ok(ILit(List(vec![])))
            } else if (elts.len() >= 2) & (elts[0] == Atom(Sym("lambda".into()))) {
                let mut args = parse_formals(&elts[1])?;
                let body = parse_seq(&elts[2..])?;
                let mut fv = Vec::new();
                free_vars(&mut fv, &mut args, &body);
                Ok(IClo(fv, args, Box::new(body)))
            } else {
                let mut exprs = elts.iter().map(parse).collect::<Result<Vec<SourceCode>,_>>()?;
                let first = exprs.remove(0);
                Ok(IApp(Box::new(first), exprs.into()))
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
    if let Some(i) = argvars.iter().position(|e| e == n) { return Some(Arg(i)) }
    if let Some(i) = envvars.iter().position(|e| e == n) { return Some(Env(i)) }
    None
}

// Err("Unbound variable: ".to_owned() + n)

fn compile(envvars: &[String], argvars: &[String], s: &SourceCode) -> Result<TargetCode, String> {
    match *s {
        ILit(ref v) => Ok(ILit(v.clone())),
        IVar(ref n) =>
            match name_to_envindex(envvars, argvars, n) {
                Some(loc) => Ok(IVar(loc)),
                None => // Primitive or unbound
                    match lookup_primitive(n) {
                        Some((i,_p)) => Ok(ILit(Atom(Prim(i)))),
                        None => Err("Unbound variable: ".to_owned() + n)
                    }
            }
        IApp(ref ratorbox, ref rands) => {
            let newrator = compile(envvars, argvars, ratorbox)?;
            let newrands = rands.iter().map(|r| compile(envvars, argvars, r))
                .collect::<Result<Vec<TargetCode>,_>>()?;
            Ok(IApp(Box::new(newrator), newrands))
        }
        IClo(ref captures_and_prims, ref formals, ref bodybox) => {
            let captures = captures_and_prims.iter()
                .filter(|n| name_to_envindex(envvars, argvars, n).is_some())
                .map(|n| n.clone())
                .collect::<Vec<String>>();
            let newbody = compile(&captures, formals, bodybox)?;
            Ok(IClo(captures.iter().map(|n| name_to_envindex(envvars, argvars, n)).flat_map(|o| o)
                    .collect::<Vec<EnvIndex>>(),
                    formals.len(),
                    Box::new(newbody)))
        }
    }
}

///////////////////////////////////////////////////////////////////////////

struct Primitive {
    name: &'static str,
    arity: usize,
    handler: fn(&mut Heap, &[Oop]) -> Result<Oop, String>,
}

static PRIMITIVES: &[Primitive] = &[
    Primitive { name: "+", arity: 2, handler: prim_add },
    Primitive { name: "print", arity: 1, handler: prim_print },
    Primitive { name: "newline", arity: 0, handler: prim_newline },
    Primitive { name: "println", arity: 1, handler: prim_println },
];

fn lookup_primitive(n: &str) -> Option<(usize, &Primitive)> {
    PRIMITIVES.iter().enumerate().find(|p| (*(p.1)).name == n)
}

fn err_arity<T>() -> Result<T, String> {
    Err("Arity mismatch".into())
}

fn err_type<T>() -> Result<T, String> {
    Err("Type mismatch".into())
}

fn prim_add(_h: &mut Heap, args: &[Oop]) -> Result<Oop, String> {
    if !args[0].is_num() { return err_type() }
    if !args[1].is_num() { return err_type() }
    Ok(Oop::num(args[0].numval() + args[1].numval()))
}

fn prim_print(h: &mut Heap, args: &[Oop]) -> Result<Oop, String> {
    print!("{}", OopHeap(args[0], h));
    Ok(Oop::num(0))
}

fn prim_newline(_h: &mut Heap, _args: &[Oop]) -> Result<Oop, String> {
    println!("");
    Ok(Oop::num(0))
}

fn prim_println(h: &mut Heap, args: &[Oop]) -> Result<Oop, String> {
    println!("{}", OopHeap(args[0], h));
    Ok(Oop::num(0))
}

///////////////////////////////////////////////////////////////////////////

type RawOop = u32;
type RawNum = i32;
type RawOfs = u32;

// 33222222222211111111110000000000 |
// 10987654321098765432109876543210 |
// -----------------------------------------------------------
// nnnnnnnnnnnnnnnnnnnnnnnnnnnnnnn1 | integer
// pppppppppppppppppppppppppppppp00 | pointer to oops
// pppppppppppppppppppppppppppppp10 | pointer to bytes

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
struct Oop {
    raw: RawOop
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
enum DecodedOop {
    Immediate(RawNum),
    Bytes(RawOop),
    Oops(RawOop)
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
enum Header {
    Bytes(usize),
    Oops(usize),
    Forward(Oop)
}

struct Heap {
    next: RawOop,
    space: Vec<Oop>,
}

impl std::fmt::Debug for Oop {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self.decode() {
            DecodedOop::Immediate(n) => write!(f, "#{}", n),
            DecodedOop::Bytes(v) => write!(f, "={}", v),
            DecodedOop::Oops(v) => write!(f, "@{}", v)
        }
    }
}

impl std::fmt::Debug for Heap {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "Heap {{\n")?;
        let mut i = 0;
        loop {
            if i >= self.space.len() { break; }
            let h = self.space[i].to_header();
            match h {
                Header::Forward(_oop) => {
                    write!(f, "{:8}: {:?}", i, h)?;
                    write!(f, "!!!! Cannot continue printing after forwarding-pointer\n")?;
                    break;
                }
                Header::Bytes(len) => {
                    write!(f, "{:8}: {:?}", i, h)?;
                    for b in self.bytes_r(i+1, len) {
                        write!(f, " {:02x}", b)?;
                    }
                    i += Heap::bytes_to_oops(len) as usize + 1;
                }
                Header::Oops(0) => {
                    // Unused slot
                    i += 1;
                    continue;
                }
                Header::Oops(len) => {
                    write!(f, "{:8}: {:?} ", i, h)?;
                    for n in 0..len {
                        write!(f, " {:?}", self.space[i + n + 1])?;
                    }
                    i += len + 1;
                }
            }
            write!(f, "\n")?;
        }
        write!(f, "{:8}  (end)\n", self.space.len())?;
        write!(f, "}}\n")
    }
}

struct OopHeap<'a>(Oop, &'a Heap);

fn printable_utf8<'a>(bs: &'a [u8]) -> Option<&'a str> {
    match std::str::from_utf8(bs) {
        Ok(s) =>
            if s.chars().all(|c| c.is_alphanumeric()) { Some(s) } else { None }
        Err(_) =>
            None
    }
}

fn valid_bytecode(bs: &[u8]) -> Option<Vec<(Bytecode, usize)>> {
    let mut items = Vec::new();
    let mut index = 0;
    loop {
        if index >= bs.len() { return Some(items) }
        let (b, arg) = decode_op(bs, &mut index)?;
        items.push((b, arg));
    }
}

impl<'a> std::fmt::Display for OopHeap<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let &OopHeap(oop, h) = self;
        if oop.is_num() {
            write!(f, "{}", oop.numval())
        } else {
            match oop.header(h) {
                Header::Bytes(_len) => {
                    let bs = oop.bytes_r(h);
                    match printable_utf8(bs) {
                        Some(s) => write!(f, "{:?}", s),
                        None =>
                            match valid_bytecode(bs) {
                                Some(items) => write!(f, "{:?}", items),
                                None => {
                                    write!(f, "#[")?;
                                    for b in bs { write!(f, "{:02x}", b)?; }
                                    write!(f, "]")
                                }
                            }
                    }
                }
                Header::Oops(len) => {
                    let oops = oop.oops_r(h);
                    write!(f, "(")?;
                    if len > 0 {
                        write!(f, "{}", OopHeap(oops[0], h))?;
                        for i in 1..len { write!(f, " {}", OopHeap(oops[i], h))? }
                    }
                    write!(f, ")")
                }
                _ => {
                    panic!("Unknown oop shape: {:?}", oop)
                }
            }
        }
    }
}

impl Oop {
    fn num(val: RawNum) -> Oop {
        Oop { raw: (val << 1) as RawOop | 1 }
    }
    fn _ptr(val: RawOop, is_bytes: bool) -> Oop {
        Oop { raw: (val << 2) | (((is_bytes as RawOop) & 1) << 1) }
    }
    fn _oops_ptr(val: RawOop) -> Oop {
        Oop::_ptr(val, false)
    }
    fn _bytes_ptr(val: RawOop) -> Oop {
        Oop::_ptr(val, true)
    }

    fn decode(&self) -> DecodedOop {
        if (self.raw & 1) == 1 {
            DecodedOop::Immediate((self.raw as RawNum) >> 1)
        } else if (self.raw & 3) == 2 {
            DecodedOop::Bytes(self.raw >> 2)
        } else if (self.raw & 3) == 0 {
            DecodedOop::Oops(self.raw >> 2)
        } else {
            panic!("Unknown oop type: {:?}", self.raw)
        }
    }

    fn copy(&self) -> Oop {
        Oop { raw: self.raw }
    }

    fn is_num(&self) -> bool {
        (self.raw & 1) == 1
    }
    fn _is_ptr(&self) -> bool {
        !self.is_num()
    }

    fn numval(&self) -> RawNum {
        if !self.is_num() { panic!("Attempt to access numeric value of non-number") }
        (self.raw as RawNum) >> 1
    }

    fn _ptrval(&self) -> RawOop {
        self.raw >> 2
    }

    fn _deref_r(&self, h: &Heap, index: usize) -> Oop {
        h.space[self._ptrval() as usize + index].copy()
    }
    fn _deref_w<'a>(&self, h: &'a mut Heap, index: usize) -> &'a mut Oop {
        &mut h.space[self._ptrval() as usize + index]
    }

    fn header(&self, h: &Heap) -> Header {
        if !self._is_ptr() { panic!("Attempt to access contents of non-pointer") }
        let header_oop = self._deref_r(h, 0);
        header_oop.to_header()
    }

    fn to_header(&self) -> Header {
        if self._is_ptr() {
            Header::Forward(*self)
        } else {
            let v = self.numval();
            if v < 0 {
                Header::Bytes((-1 - v) as usize)
            } else {
                Header::Oops(v as usize)
            }
        }
    }

    fn bytes_r<'a>(&self, h: &'a Heap) -> &'a [u8] {
        if let Header::Bytes(len) = self.header(h) {
            h.bytes_r(self._ptrval() as usize + 1, len)
        } else {
            panic!("Attempted to extract bytes_r of non-bytes oop {:?}", self);
        }
    }
    fn bytes_w<'a>(&self, h: &'a mut Heap) -> &'a mut [u8] {
        if let Header::Bytes(len) = self.header(h) {
            h.bytes_w(self._ptrval() as usize + 1, len)
        } else {
            panic!("Attempted to extract bytes_w of non-bytes oop {:?}", self);
        }
    }

    fn oops_r<'a>(&self, h: &'a Heap) -> &'a [Oop] {
        if let Header::Oops(len) = self.header(h) {
            let lo = self._ptrval() as usize + 1;
            &h.space[lo..(lo+len)]
        } else {
            panic!("Attempted to read slots of non-oops oop {:?}", self);
        }
    }
    fn oops_w<'a>(&self, h: &'a mut Heap) -> &'a mut [Oop] {
        if let Header::Oops(len) = self.header(h) {
            let lo = self._ptrval() as usize + 1;
            &mut h.space[lo..(lo+len)]
        } else {
            panic!("Attempted to write slots of non-oops oop {:?}", self);
        }
    }
}

impl Header {
    fn to_oop(&self) -> Oop {
        match self {
            &Header::Bytes(len) => Oop::num(-1 - (len as RawNum)),
            &Header::Oops(len) => Oop::num(len as RawNum),
            &Header::Forward(oop) => oop
        }
    }
}

impl Heap {
    fn new(size: RawOfs) -> Heap {
        Heap {
            next: 0,
            space: std::iter::repeat(Oop::num(0)).take(size as usize).collect::<Vec<_>>(),
        }
    }

    fn len(&self) -> RawOfs {
        self.space.len() as RawOfs
    }

    fn _alloc(&mut self, len: RawOfs) -> Option<RawOop> {
        let thisval = self.next;
        let nextval = thisval + len + 1;
        if nextval <= self.len() {
            self.next = nextval;
            Some(thisval)
        } else {
            None
        }
    }

    fn alloc_oops(&mut self, len: usize) -> Option<Oop> {
        if len >= self.space.len() { return None }
        self._alloc(len as RawOfs).map(|p| {
            let result = Oop::_oops_ptr(p);
            *(result._deref_w(self, 0)) = Header::Oops(len).to_oop();
            result
        })
    }

    fn inject_oops(&mut self, oops: &[Oop]) -> Option<Oop> {
        let oop = self.alloc_oops(oops.len())?;
        let w = oop.oops_w(self);
        for i in 0..oops.len() {
            w[i] = oops[i];
        }
        Some(oop)
    }

    fn bytes_to_oops(len: usize) -> RawOfs {
        let oopsize = std::mem::size_of::<Oop>();
        ((len + (oopsize - 1)) / oopsize) as RawOfs
    }

    fn alloc_bytes(&mut self, len: usize) -> Option<Oop> {
        let oop_count = Heap::bytes_to_oops(len);
        if oop_count as usize >= self.space.len() { return None }
        self._alloc(oop_count).map(|p| {
            let result = Oop::_bytes_ptr(p);
            *(result._deref_w(self, 0)) = Header::Bytes(len).to_oop();
            result
        })
    }

    fn inject_bytes(&mut self, bs: &[u8]) -> Option<Oop> {
        let oop = self.alloc_bytes(bs.len())?;
        oop.bytes_w(self).copy_from_slice(bs);
        Some(oop)
    }

    fn bytes_r<'a>(&'a self, lo: usize, len: usize) -> &'a [u8] {
        let lo_byte = lo * std::mem::size_of::<Oop>();
        let all = unsafe {
            std::slice::from_raw_parts(self.space.as_ptr() as *const u8,
                                       self.space.len() * std::mem::size_of::<Oop>())
        };
        &all[lo_byte..(lo_byte + len)]
    }

    fn bytes_w<'a>(&'a mut self, lo: usize, len: usize) -> &'a mut [u8] {
        let lo_byte = lo * std::mem::size_of::<Oop>();
        let all = unsafe {
            std::slice::from_raw_parts_mut(self.space.as_ptr() as *mut u8,
                                           self.space.len() * std::mem::size_of::<Oop>())
        };
        &mut all[lo_byte..(lo_byte + len)]
    }
}

struct Collection<'a> {
    old: &'a mut Heap,
    new: Heap,
}

impl<'a> Collection<'a> {
    fn new(old: &'a mut Heap) -> Collection<'a> {
        let oldlen = old.len();
        Collection {
            old: old,
            new: Heap::new(oldlen)
        }
    }

    fn gc_copy(&mut self, o: Oop) -> Oop {
        if o.is_num() { return o }
        assert!(o._is_ptr());
        match o.header(self.old) {
            Header::Forward(oop) => oop,
            Header::Bytes(len) => {
                let target = self.new.alloc_bytes(len).unwrap();
                target.bytes_w(&mut self.new).copy_from_slice(o.bytes_r(self.old));
                *(o._deref_w(self.old, 0)) = Header::Forward(target).to_oop();
                target
            }
            Header::Oops(len) => {
                let target = self.new.alloc_oops(len).unwrap();
                *(o._deref_w(self.old, 0)) = Header::Forward(target).to_oop();
                for i in 0..len {
                    let slot = o._deref_r(self.old, i+1);
                    *(target._deref_w(&mut self.new, i+1)) = self.gc_copy(slot);
                }
                target
            }
        }
    }
}

///////////////////////////////////////////////////////////////////////////

fn encode_op(code: &mut Vec<u8>, b: Bytecode, uarg: usize) -> () {
    let opcode = (b.clone() as u8) << 5;
    if uarg < 0x1f {
        code.push(opcode | uarg as u8);
    } else if uarg < 0xffff {
        code.push(opcode | 0x1f);
        code.push((uarg >> 8) as u8);
        code.push(uarg as u8);
    } else {
        panic!("Cannot emit {:?} with argument {}", b, uarg)
    }
}

fn extract_u8(code: &[u8], index: &mut usize) -> Option<u8> {
    if *index >= code.len() {
        None
    } else {
        let val = code[*index];
        *index += 1;
        Some(val)
    }
}

fn decode_bytecode(n: u8) -> Option<Bytecode> {
    match n {
        0 => Some(OpLiteral),
        1 => Some(OpEnvRef),
        2 => Some(OpArgRef),
        3 => Some(OpFrame),
        4 => Some(OpJump),
        5 => Some(OpCall),
        6 => Some(OpReturn),
        7 => Some(OpClosure),
        _ => None
    }
}

fn decode_op(code: &[u8], index: &mut usize) -> Option<(Bytecode, usize)> {
    let op = extract_u8(code, index)?;
    let b = decode_bytecode(op >> 5)?;
    let arg = op & 0x1f;
    if arg < 0x1f {
        Some((b, arg as usize))
    } else {
        let arg = extract_u8(code, index)? as u16;
        let arg = (arg << 8) | (extract_u8(code, index)? as u16);
        if arg < 0xffff {
            Some((b, arg as usize))
        } else {
            panic!("Opcode {:?} argument too large", b)
        }
    }
}

///////////////////////////////////////////////////////////////////////////

impl ProgramValue {
    fn inject(&self, h: &mut Heap) -> Option<Oop> {
        match self {
            &Atom(Lit(Num(n))) => {
                Some(Oop::num(n as RawNum))
            }
            &Atom(Lit(Sym(ref s))) => {
                h.inject_bytes(s.as_bytes())
            }
            &Atom(Prim(n)) => {
                Some(Oop::num(n as RawNum))
            }
            &Atom(Clo(ref envspec, arity, ref codebox)) => {
                // Closure layout:
                // Oop |
                // --------------------
                //   0 | arity
                //   1 | codepointer --> bytes
                //   2 | litpointer --> oops
                //   3 | env[0]
                // ... | ... more captured environment values

                let (codepointer, lit) = codebox.inject(h)?;
                let clo = h.alloc_oops(envspec.len() + 3)?;
                {
                    let w = clo.oops_w(h);
                    w[0] = Oop::num(arity as RawNum);
                    w[1] = codepointer;
                    w[2] = lit;
                }
                for i in 0..envspec.len() {
                    clo.oops_w(h)[i + 3] = envspec[i].inject(h)?;
                }
                Some(clo)
            }
            &List(ref elts) => {
                let p = h.alloc_oops(elts.len())?;
                for i in 0..elts.len() {
                    p.oops_w(h)[i] = elts[i].inject(h)?;
                }
                Some(p)
            }
        }
    }
}

impl TargetCode {
    fn inject(&self, h: &mut Heap) -> Option<(Oop, Oop)> {
        let mut literals = Vec::new();
        let mut codevec = Vec::new();
        self._inject(h, &mut codevec, &mut literals, true)?;
        let codepointer = h.inject_bytes(&codevec)?;
        let lit = h.inject_oops(&literals)?;
        Some((codepointer, lit))
    }

    fn _inject(&self,
              h: &mut Heap,
              codevec: &mut Vec<u8>,
              literals: &mut Vec<Oop>,
              tail: bool)
              -> Option<()>
    {
        match self {
            &ILit(ref v) => {
                encode_op(codevec, OpLiteral, literals.len());
                if tail { encode_op(codevec, OpReturn, 0) }
                literals.push(v.inject(h)?);
                Some(())
            }
            &IVar(Env(n)) => {
                encode_op(codevec, OpEnvRef, n);
                if tail { encode_op(codevec, OpReturn, 0) }
                Some(())
            }
            &IVar(Arg(n)) => {
                encode_op(codevec, OpArgRef, n);
                if tail { encode_op(codevec, OpReturn, 0) }
                Some(())
            }
            &IApp(ref ratorbox, ref rands) => {
                encode_op(codevec, OpFrame, rands.len());
                ratorbox._inject(h, codevec, literals, false)?;
                for rand in rands {
                    rand._inject(h, codevec, literals, false)?;
                }
                encode_op(codevec, if tail { OpJump } else { OpCall }, 0);
                Some(())
            }
            &IClo(ref captures, formals, ref bodybox) => {
                encode_op(codevec, OpClosure, literals.len());
                let (codepointer, lit) = bodybox.inject(h)?;
                literals.push(Oop::num(formals as RawNum));
                literals.push(codepointer);
                literals.push(lit);
                literals.push(Oop::num(captures.len() as RawNum));
                for capture in captures {
                    literals.push(Oop::num(match capture {
                        &Env(n) => -1 - (n as RawNum),
                        &Arg(n) => n as RawNum
                    }));
                }
                Some(())
            }
        }
    }
}

///////////////////////////////////////////////////////////////////////////

struct VM {
    h: Heap,
    a: Oop,
    i: usize,
    f: Oop,
}

impl VM {
    fn boot(mut h: Heap, code: Oop, lits: Oop) -> VM {
        let c = h.inject_oops(&[Oop::num(0), code, lits]).unwrap();
        let a = h.inject_oops(&[c, Oop::num(0), Oop::num(0)]).unwrap();
        let f = h.inject_oops(&[Oop::num(0), Oop::num(0), Oop::num(0)]).unwrap();
        VM { h: h, a: a, i: 0, f: f }
    }

    fn _arg(&self, i: usize) -> Oop {
        self.a.oops_r(&self.h)[i]
    }
    fn arg(&self, i: usize) -> Oop {
        self._arg(i + 1)
    }
    fn argc(&self) -> usize {
        self.a.oops_r(&self.h).len() - 3 // 1 for the closure, two for saved I/A
    }
    fn _closure(&self) -> &[Oop] {
        self._arg(0).oops_r(&self.h)
    }
    fn code(&self) -> &[u8] {
        self._closure()[1].bytes_r(&self.h)
    }
    fn lit(&self, i: usize) -> Oop {
        self._closure()[2].oops_r(&self.h)[i]
    }
    fn env(&self, i: usize) -> Oop {
        self._closure()[i+3]
    }
    fn store(&mut self, v: Oop) -> () {
        let w = self.f.oops_w(&mut self.h);
        let len = w.len();
        let index = w[len-1].numval() as usize;
        w[index] = v;
        w[len-1] = Oop::num((index + 1) as RawNum);
    }
    fn gc(&mut self) -> () {
        self.h = {
            let mut c = Collection::new(&mut self.h);
            self.a = c.gc_copy(self.a);
            self.f = c.gc_copy(self.f);
            c.new
        }
    }
    fn alloc_oops(&mut self, n: usize) -> Oop {
        self.h.alloc_oops(n).unwrap_or_else(|| {
            self.gc();
            self.h.alloc_oops(n).unwrap_or_else(|| {
                panic!("Could not allocate {} slots after gc", n)
            })
        })
    }
    fn pushframe(&mut self, n: usize) -> () {
        let new_f = self.alloc_oops(n + 3); // 1 for closure, 2 for saved I/A
        let w = new_f.oops_w(&mut self.h);
        let len = w.len();
        w[len-2] = self.f;
        w[len-1] = Oop::num(0);
        self.f = new_f;
    }
    fn trap_check(&mut self) -> () {
        if self._arg(0).is_num() { // Primitive!
            let p = &PRIMITIVES[self._arg(0).numval() as usize];
            println!("Primitive {:?}", p.name);
            if self.argc() != p.arity {
                panic!("Primitive '{}' expects {} args, given {}", p.name, p.arity, self.argc());
            }
            let args = {
                let v = self.a.oops_r(&self.h);
                v[1..(v.len() - 2)].to_vec()
            };
            let result = match (p.handler)(&mut self.h, &args) {
                Ok(r) => r,
                Err(msg) => panic!("Primitive '{}' error: {}", p.name, msg)
            };
            self.store(result);
            self.ret();
        }
    }
    fn jump(&mut self) -> () {
        let (saved_i, saved_a) = {
            let r = self.a.oops_r(&self.h);
            (r[r.len() - 2], r[r.len() - 1])
        };
        let w = self.f.oops_w(&mut self.h);
        let len = w.len();
        let tmp = w[len-2];
        w[len-2] = saved_i;
        w[len-1] = saved_a;
        self.a = self.f;
        self.f = tmp;
        self.i = 0
    }
    fn call(&mut self) -> () {
        let w = self.f.oops_w(&mut self.h);
        let len = w.len();
        w[len-1] = self.a;
        self.a = self.f;
        self.f = w[len-2];
        w[len-2] = Oop::num(self.i as RawNum);
        self.i = 0
    }
    fn ret(&mut self) -> () {
        let r = self.a.oops_r(&self.h);
        self.i = r[r.len() - 2].numval() as usize;
        self.a = r[r.len() - 1];
    }
    fn clo(&mut self, n: usize) -> Oop {
        let arity = self.lit(n);
        let code = self.lit(n+1);
        let lits = self.lit(n+2);
        let capturecount = self.lit(n+3).numval() as usize;
        let c = self.alloc_oops(capturecount + 3);
        {
            let w = c.oops_w(&mut self.h);
            w[0] = arity;
            w[1] = code;
            w[2] = lits;
        }
        for i in 0..capturecount {
            let spec = self.lit(i+4).numval();
            let v = if spec < 0 { self.env((-1 - spec) as usize) } else { self.arg(spec as usize) };
            c.oops_w(&mut self.h)[i+3] = v;
        }
        c
    }
    fn next_instruction(&mut self) -> (Bytecode, usize) {
        let mut ip = self.i;
        let instr = decode_op(self.code(), &mut ip).unwrap();
        self.i = ip;
        instr
    }
    fn run(&mut self) -> Oop {
        loop {
            if self.a.is_num() {
                return self.f.oops_r(&self.h)[0]
            }
            let (op, n) = self.next_instruction();
            match op {
                OpLiteral => {
                    let v = self.lit(n);
                    self.store(v);
                }
                OpEnvRef => {
                    let v = self.env(n);
                    self.store(v);
                }
                OpArgRef => {
                    let v = self.arg(n);
                    self.store(v);
                }
                OpFrame => {
                    self.pushframe(n);
                }
                OpJump => {
                    self.jump();
                    self.trap_check();
                }
                OpCall => {
                    self.call();
                    self.trap_check();
                }
                OpReturn => {
                    self.ret();
                }
                OpClosure => {
                    let v = self.clo(n);
                    self.store(v);
                }
            }
        }
    }
}

///////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod tests {
    use super::*;

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

    fn read_one_sexp(s: &str) -> Result<InputSexp, String> {
        read_sexp(&mut s.chars().peekable())
    }

    #[test]
    fn read_atomic_sexp() {
        assert!(read_one_sexp("").is_err());
        assert_eq!(Sexp::Atom(Num(0)), read_one_sexp("0").unwrap());
        assert_eq!(Sexp::Atom(Sym("a".into())), read_one_sexp("a b").unwrap());
    }

    #[test]
    fn read_nonatomic_sexp() {
        assert_eq!(Sexp::List(vec![]), read_one_sexp("()").unwrap());
        assert_eq!(Sexp::List(vec![Sexp::Atom(Sym("a".into())),
                                   Sexp::Atom(Sym("b".into()))]),
                   read_one_sexp("(a b)").unwrap());
        assert_eq!(Sexp::List(vec![Sexp::Atom(Sym("a".into())),
                                   Sexp::List(vec![Sexp::Atom(Sym("b".into()))]),
                                   Sexp::Atom(Sym("c".into()))]),
                   read_one_sexp("(a (b) c)").unwrap());
    }

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
    fn heap_alloc_oops_simple() {
        let mut h = Heap::new(16);
        assert_eq!(Oop::_oops_ptr(0), h.alloc_oops(7).unwrap());
        assert_eq!(Header::Oops(7), Oop::_oops_ptr(0).header(&h));
        assert_eq!(Oop::_oops_ptr(8), h.alloc_oops(7).unwrap());
        assert_eq!(Header::Oops(7), Oop::_oops_ptr(8).header(&h));
        assert_eq!(None, h.alloc_oops(0));
    }

    #[test]
    fn heap_copy_simple() {
        let mut old = Heap::new(16);
        old.alloc_oops(7);
        let p = old.alloc_oops(7).unwrap();
        assert_eq!(Oop::_oops_ptr(8), p);
        let mut c = Collection::new(&mut old);
        let p = c.gc_copy(p);
        let mut new = c.new;
        assert_eq!(Oop::_oops_ptr(0), p);
        assert_eq!(Header::Oops(7), p.header(&new));
        assert_eq!(8, new.next);
        assert_eq!(Oop::_oops_ptr(8), new.alloc_oops(3).unwrap());
        assert_eq!(12, new.next);
    }

    #[test]
    fn test_inject_programvalue() {
        let mut h = Heap::new(16);
        let p = Atom(Lit(Sym("hello".into()))).inject(&mut h).unwrap();
        assert_eq!(3, h.next);
        let q = Atom(Lit(Num(12345678))).inject(&mut h).unwrap();
        assert_eq!(3, h.next);
        let r = Atom(Lit(Sym("pals".into()))).inject(&mut h).unwrap();
        assert_eq!(5, h.next);

        assert_eq!(DecodedOop::Bytes(0), p.decode());
        assert_eq!(Header::Bytes(5), p.header(&h));
        assert_eq!("hello".as_bytes(), p.bytes_r(&h));

        assert!(q.is_num());
        assert_eq!(12345678, q.numval());

        assert_eq!(DecodedOop::Bytes(3), r.decode());
        assert_eq!(Header::Bytes(4), r.header(&h));
        assert_eq!("pals".as_bytes(), r.bytes_r(&h));

        let mut c = Collection::new(&mut h);
        let r = c.gc_copy(r);
        let q = c.gc_copy(q);
        let p = c.gc_copy(p);
        let /* mut */ h = c.new;

        assert_eq!(5, h.next);

        assert_eq!(DecodedOop::Bytes(2), p.decode());
        assert_eq!(Header::Bytes(5), p.header(&h));
        assert_eq!("hello".as_bytes(), p.bytes_r(&h));

        assert!(q.is_num());
        assert_eq!(12345678, q.numval());

        assert_eq!(DecodedOop::Bytes(0), r.decode());
        assert_eq!(Header::Bytes(4), r.header(&h));
        assert_eq!("pals".as_bytes(), r.bytes_r(&h));
    }

    #[test]
    fn roundtrip_bytecode() {
        let mut code = Vec::new();
        encode_op(&mut code, OpLiteral, 0);
        encode_op(&mut code, OpEnvRef, 1);
        encode_op(&mut code, OpArgRef, 2);
        encode_op(&mut code, OpFrame, 30);
        encode_op(&mut code, OpJump, 31);
        encode_op(&mut code, OpCall, 32);
        encode_op(&mut code, OpReturn, 40);
        encode_op(&mut code, OpClosure, 2000);
        assert_eq!([0x00, 0x21, 0x42, 0x7e, 0x9f, 0, 31, 0xbf, 0, 32, 0xdf, 0, 40, 0xff, 7, 208],
                   code.as_slice());
        let mut index = 0;
        assert_eq!((OpLiteral, 0), decode_op(&code, &mut index).unwrap());
        assert_eq!((OpEnvRef, 1), decode_op(&code, &mut index).unwrap());
        assert_eq!((OpArgRef, 2), decode_op(&code, &mut index).unwrap());
        assert_eq!((OpFrame, 30), decode_op(&code, &mut index).unwrap());
        assert_eq!((OpJump, 31), decode_op(&code, &mut index).unwrap());
        assert_eq!((OpCall, 32), decode_op(&code, &mut index).unwrap());
        assert_eq!((OpReturn, 40), decode_op(&code, &mut index).unwrap());
        assert_eq!((OpClosure, 2000), decode_op(&code, &mut index).unwrap());

        assert_eq!(OpLiteral, decode_bytecode(OpLiteral as u8).unwrap());
        assert_eq!(OpEnvRef, decode_bytecode(OpEnvRef as u8).unwrap());
        assert_eq!(OpArgRef, decode_bytecode(OpArgRef as u8).unwrap());
        assert_eq!(OpFrame, decode_bytecode(OpFrame as u8).unwrap());
        assert_eq!(OpJump, decode_bytecode(OpJump as u8).unwrap());
        assert_eq!(OpCall, decode_bytecode(OpCall as u8).unwrap());
        assert_eq!(OpReturn, decode_bytecode(OpReturn as u8).unwrap());
        assert_eq!(OpClosure, decode_bytecode(OpClosure as u8).unwrap());
    }

    #[test]
    fn test_inject_code_simple() {
        let parsed = parse(&read_one_sexp("((lambda (a b) (+ a b)) 123 234)").unwrap()).unwrap();
        let compiled = compile(&vec![], &vec![], &parsed).unwrap();
        let mut h = Heap::new(1024);
        let (codepointer, lit) = compiled.inject(&mut h).unwrap();
        println!("{:?} {:?} {:?}", codepointer, lit, h);
        println!("{}", OopHeap(codepointer, &h));
        println!("{}", OopHeap(lit, &h));
        let mut vm = VM::boot(h, codepointer, lit);
        let result = vm.run();
        assert!(result.is_num());
        assert_eq!(357, result.numval());
    }

    #[test]
    fn test_bytecode_range() {
        // Supposed to ensure that we have 8 or fewer opcodes!
        assert!((OpClosure as u8) < 8);
    }
}
