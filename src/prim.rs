use super::heap::Heap;
use super::heap::Oop;
use super::heap::OopHeap;

pub struct Primitive {
    pub name: &'static str,
    pub arity: usize,
    pub handler: fn(&mut Heap, &[Oop]) -> Result<Oop, String>,
}

static PRIMITIVES: &[Primitive] = &[
    Primitive { name: "+", arity: 2, handler: prim_add },
    Primitive { name: "print", arity: 1, handler: prim_print },
    Primitive { name: "newline", arity: 0, handler: prim_newline },
    Primitive { name: "println", arity: 1, handler: prim_println },
];

pub fn lookup_primitive(n: &str) -> Option<(usize, &'static Primitive)> {
    PRIMITIVES.iter().enumerate().find(|p| (*(p.1)).name == n)
}

pub fn lookup_primitive_index(i: usize) -> Option<&'static Primitive> {
    PRIMITIVES.get(i)
}

///////////////////////////////////////////////////////////////////////////

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
