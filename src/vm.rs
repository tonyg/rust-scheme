use crate::prim::lookup_primitive_index;

use super::code::Bytecode;
use super::gc::Collection;
use super::heap::Heap;
use super::heap::Oop;
use super::heap::RawNum;
use super::heap::decode_op;

pub struct VM {
    h: Heap,
    a: Oop,
    i: usize,
    f: Oop,
}

impl VM {
    pub fn boot(mut h: Heap, code: Oop, lits: Oop) -> VM {
        let c = h.inject_oops(&[Oop::num(0), code, lits]).unwrap();
        let a = h.inject_oops(&[c, Oop::num(0), Oop::num(0)]).unwrap();
        let f = h.inject_oops(&[Oop::num(0), Oop::num(0), Oop::num(0)]).unwrap();
        VM { h, a, i: 0, f }
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
        let mut c = Collection::new(&mut self.h);
        self.a = c.gc_copy(self.a);
        self.f = c.gc_copy(self.f);
        self.h = c.new;
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
            let p = lookup_primitive_index(self._arg(0).numval() as usize).unwrap();
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
        self.i = 0;
        self.trap_check()
    }
    fn call(&mut self) -> () {
        let w = self.f.oops_w(&mut self.h);
        let len = w.len();
        w[len-1] = self.a;
        self.a = self.f;
        self.f = w[len-2];
        w[len-2] = Oop::num(self.i as RawNum);
        self.i = 0;
        self.trap_check()
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
    pub fn run(&mut self) -> Oop {
        loop {
            if self.a.is_num() {
                return self.f.oops_r(&self.h)[0]
            }
            let (op, n) = self.next_instruction();
            match op {
                Bytecode::OpLiteral => self.store(self.lit(n)),
                Bytecode::OpEnvRef => self.store(self.env(n)),
                Bytecode::OpArgRef => self.store(self.arg(n)),
                Bytecode::OpFrame => self.pushframe(n),
                Bytecode::OpJump => self.jump(),
                Bytecode::OpCall => self.call(),
                Bytecode::OpReturn => self.ret(),
                Bytecode::OpClosure => {
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

    use crate::code::compile;
    use crate::code::parse;
    use crate::sexp::read_one_sexp;
    use crate::heap::OopHeap;

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
}
