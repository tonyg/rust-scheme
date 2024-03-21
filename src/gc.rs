use super::heap::{Heap, Header, Oop};

pub struct Collection<'a> {
    old: &'a mut Heap,
    pub new: Heap,
}

impl<'a> Collection<'a> {
    pub fn new(old: &'a mut Heap) -> Collection<'a> {
        let oldlen = old.len();
        Collection { old, new: Heap::new(oldlen) }
    }

    pub fn gc_copy(&mut self, o: Oop) -> Oop {
        if o.is_num() { return o }
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
