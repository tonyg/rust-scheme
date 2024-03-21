use super::sexp::Sexp;
use super::sexp::Literal;

use super::code::Bytecode;
use super::code::EnvIndex;
use super::code::Instruction;
use super::code::ProgramAtom;

type RawOop = u32;
pub type RawNum = i32;

// 33222222222211111111110000000000 |
// 10987654321098765432109876543210 |
// -----------------------------------------------------------
// nnnnnnnnnnnnnnnnnnnnnnnnnnnnnnn1 | integer
// pppppppppppppppppppppppppppppp00 | pointer to oops
// pppppppppppppppppppppppppppppp10 | pointer to bytes

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub struct Oop {
    raw: RawOop
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
enum DecodedOop {
    Immediate(RawNum),
    Bytes(RawOop),
    Oops(RawOop)
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum Header {
    Bytes(usize),
    Oops(usize),
    Forward(Oop)
}

pub struct Heap {
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
                    i += Heap::bytes_to_oops(len) + 1;
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

pub struct OopHeap<'a>(pub Oop, pub &'a Heap);

///////////////////////////////////////////////////////////////////////////

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
    pub fn num(val: RawNum) -> Oop {
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

    pub fn is_num(&self) -> bool {
        (self.raw & 1) == 1
    }

    pub fn numval(&self) -> RawNum {
        if !self.is_num() { panic!("Attempt to access numeric value of non-number") }
        (self.raw as RawNum) >> 1
    }

    fn _ptrval(&self) -> RawOop {
        self.raw >> 2
    }

    pub fn _deref_r(&self, h: &Heap, index: usize) -> Oop {
        h.space[self._ptrval() as usize + index].copy()
    }
    pub fn _deref_w<'a>(&self, h: &'a mut Heap, index: usize) -> &'a mut Oop {
        &mut h.space[self._ptrval() as usize + index]
    }

    pub fn header(&self, h: &Heap) -> Header {
        if self.is_num() { panic!("Attempt to access contents of non-pointer") }
        let header_oop = self._deref_r(h, 0);
        header_oop.to_header()
    }

    fn to_header(&self) -> Header {
        if !self.is_num() {
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

    pub fn bytes_r<'a>(&self, h: &'a Heap) -> &'a [u8] {
        if let Header::Bytes(len) = self.header(h) {
            h.bytes_r(self._ptrval() as usize + 1, len)
        } else {
            panic!("Attempted to extract bytes_r of non-bytes oop {:?}", self);
        }
    }

    pub fn bytes_w<'a>(&self, h: &'a mut Heap) -> &'a mut [u8] {
        if let Header::Bytes(len) = self.header(h) {
            h.bytes_w(self._ptrval() as usize + 1, len)
        } else {
            panic!("Attempted to extract bytes_w of non-bytes oop {:?}", self);
        }
    }

    pub fn oops_r<'a>(&self, h: &'a Heap) -> &'a [Oop] {
        if let Header::Oops(len) = self.header(h) {
            let lo = self._ptrval() as usize + 1;
            &h.space[lo..(lo+len)]
        } else {
            panic!("Attempted to read slots of non-oops oop {:?}", self);
        }
    }

    pub fn oops_w<'a>(&self, h: &'a mut Heap) -> &'a mut [Oop] {
        if let Header::Oops(len) = self.header(h) {
            let lo = self._ptrval() as usize + 1;
            &mut h.space[lo..(lo+len)]
        } else {
            panic!("Attempted to write slots of non-oops oop {:?}", self);
        }
    }
}

impl Header {
    pub fn to_oop(&self) -> Oop {
        match self {
            Header::Bytes(len) => Oop::num(-1 - (*len as RawNum)),
            Header::Oops(len) => Oop::num(*len as RawNum),
            Header::Forward(oop) => *oop
        }
    }
}

impl Heap {
    pub fn new(size: usize) -> Heap {
        Heap {
            next: 0,
            space: std::iter::repeat(Oop::num(0)).take(size as usize).collect::<Vec<_>>(),
        }
    }

    pub fn len(&self) -> usize {
        self.space.len()
    }

    fn _alloc(&mut self, len: usize) -> Option<RawOop> {
        let thisval = self.next;
        let nextval = thisval as usize + len + 1;
        if nextval <= self.len() {
            self.next = nextval as RawOop;
            Some(thisval)
        } else {
            None
        }
    }

    pub fn alloc_oops(&mut self, len: usize) -> Option<Oop> {
        self._alloc(len).map(|p| {
            let result = Oop::_oops_ptr(p);
            *(result._deref_w(self, 0)) = Header::Oops(len).to_oop();
            result
        })
    }

    pub fn inject_oops(&mut self, oops: &[Oop]) -> Option<Oop> {
        let oop = self.alloc_oops(oops.len())?;
        oop.oops_w(self).copy_from_slice(oops);
        Some(oop)
    }

    fn bytes_to_oops(len: usize) -> usize {
        let oopsize = std::mem::size_of::<Oop>();
        (len + (oopsize - 1)) / oopsize
    }

    pub fn alloc_bytes(&mut self, len: usize) -> Option<Oop> {
        self._alloc(Heap::bytes_to_oops(len)).map(|p| {
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

///////////////////////////////////////////////////////////////////////////

impl super::code::ProgramValue {
    pub fn inject(&self, h: &mut Heap) -> Option<Oop> {
        match self {
            Sexp::Atom(ProgramAtom::Lit(Literal::Num(n))) => {
                Some(Oop::num(*n as RawNum))
            }
            Sexp::Atom(ProgramAtom::Lit(Literal::Sym(s))) => {
                h.inject_bytes(s.as_bytes())
            }
            Sexp::Atom(ProgramAtom::Prim(n)) => {
                Some(Oop::num(*n as RawNum))
            }
            Sexp::Atom(ProgramAtom::Clo(envspec, arity, codebox)) => {
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
                    w[0] = Oop::num(*arity as RawNum);
                    w[1] = codepointer;
                    w[2] = lit;
                }
                for i in 0..envspec.len() {
                    clo.oops_w(h)[i + 3] = envspec[i].inject(h)?;
                }
                Some(clo)
            }
            Sexp::List(elts) => {
                let p = h.alloc_oops(elts.len())?;
                for i in 0..elts.len() {
                    p.oops_w(h)[i] = elts[i].inject(h)?;
                }
                Some(p)
            }
        }
    }
}

impl super::code::TargetCode {
    pub fn inject(&self, h: &mut Heap) -> Option<(Oop, Oop)> {
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
            Instruction::ILit(v) => {
                encode_op(codevec, Bytecode::OpLiteral, literals.len());
                if tail { encode_op(codevec, Bytecode::OpReturn, 0) }
                literals.push(v.inject(h)?);
                Some(())
            }
            Instruction::IVar(EnvIndex::Env(n)) => {
                encode_op(codevec, Bytecode::OpEnvRef, *n);
                if tail { encode_op(codevec, Bytecode::OpReturn, 0) }
                Some(())
            }
            Instruction::IVar(EnvIndex::Arg(n)) => {
                encode_op(codevec, Bytecode::OpArgRef, *n);
                if tail { encode_op(codevec, Bytecode::OpReturn, 0) }
                Some(())
            }
            Instruction::IApp(ratorbox, rands) => {
                encode_op(codevec, Bytecode::OpFrame, rands.len());
                ratorbox._inject(h, codevec, literals, false)?;
                for rand in rands {
                    rand._inject(h, codevec, literals, false)?;
                }
                encode_op(codevec, if tail { Bytecode::OpJump } else { Bytecode::OpCall }, 0);
                Some(())
            }
            Instruction::IClo(captures, formals, bodybox) => {
                encode_op(codevec, Bytecode::OpClosure, literals.len());
                let (codepointer, lit) = bodybox.inject(h)?;
                literals.push(Oop::num(*formals as RawNum));
                literals.push(codepointer);
                literals.push(lit);
                literals.push(Oop::num(captures.len() as RawNum));
                for capture in captures {
                    literals.push(Oop::num(match capture {
                        EnvIndex::Env(n) => -1 - (*n as RawNum),
                        EnvIndex::Arg(n) => *n as RawNum
                    }));
                }
                Some(())
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

pub fn decode_op(code: &[u8], index: &mut usize) -> Option<(Bytecode, usize)> {
    let op = extract_u8(code, index)?;
    let b: Bytecode = (op >> 5).try_into().ok()?;
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

#[cfg(test)]
mod tests {
    use super::*;

    use crate::gc::Collection;
    use crate::code::Bytecode::*;
    use crate::code::ProgramAtom::*;
    use crate::sexp::Sexp::*;
    use crate::sexp::Literal::*;

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
    }
}
