use std::borrow::Borrow;
use std::convert::AsRef;
use std::ops::{Index, Range};
use std::ptr;
use std::rc::Rc;


#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Slot<T> {
    Owned(T),
    Borrowed(Rc<T>),
}


impl<T> AsRef<T> for Slot<T> {
    fn as_ref(&self) -> &T {
        match *self {
            Slot::Owned(ref t) => t,
            Slot::Borrowed(ref rc_t) => rc_t.as_ref(),
        }
    }
}


impl<T> Slot<T> {
    fn share(&mut self) -> Rc<T> {
        unsafe {
            let shared = ptr::read(self).into_shared();
            ptr::write(self, Slot::Borrowed(shared.clone()));
            shared
        }
    }


    fn into_shared(self) -> Rc<T> {
        match self {
            Slot::Owned(t) => Rc::new(t),
            Slot::Borrowed(rc_t) => rc_t,
        }
    }
}


#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Stack<T> {
    inner: Vec<Slot<T>>,
}


impl<T> Stack<T> {
    pub fn new() -> Stack<T> {
        Stack { inner: Vec::new() }
    }


    pub fn push(&mut self, elem: T) {
        self.inner.push(Slot::Owned(elem));
    }


    pub fn cons(mut self, elem: T) -> Stack<T> {
        self.push(elem);
        self
    }


    pub fn push_shared(&mut self, elem: Rc<T>) {
        self.inner.push(Slot::Borrowed(elem));
    }


    pub fn cons_shared(mut self, elem: Rc<T>) -> Stack<T> {
        self.push_shared(elem);
        self
    }


    pub fn capture(&mut self, upto: usize) -> Stack<T> {
        let mut captures = Stack::new();

        let len = self.inner.len();

        for i in (0..upto).rev() {
            captures.inner.push(Slot::Borrowed(self.inner[len - i - 1].share()));
        }

        captures
    }


    pub fn len(&self) -> usize {
        self.inner.len()
    }


    pub fn isolate<U, F: FnOnce(&mut Stack<T>) -> U>(&mut self, block: F) -> U {
        let saved_len = self.inner.len();

        let result = block(self);

        while self.inner.len() > saved_len {
            self.inner.pop();
        }

        result
    }


    pub fn share(&mut self, idx: usize) -> Rc<T> {
        assert!(idx <= self.inner.len(),
                "Attempt to index stack out of bounds - stack holds only {} elements, not {}!",
                self.inner.len(),
                idx);
        let len = self.inner.len();
        self.inner[len - idx - 1].share()
    }
}


impl<T: PartialEq, U> Stack<(T, U)> {
    pub fn lookup<K: Borrow<T>>(&self, target: K) -> Option<&U> {
        self.inner
            .iter()
            .rev()
            .map(|slot| slot.as_ref())
            .find(|&&(ref key, ref val)| key == target.borrow())
            .map(|&(_, ref val)| val)
    }
}


impl<T> Index<usize> for Stack<T> {
    type Output = T;

    fn index(&self, idx: usize) -> &T {
        assert!(idx <= self.inner.len(),
                "Attempt to index stack out of bounds - stack holds only {} elements, not {}!",
                self.inner.len(),
                idx);
        self.inner[self.inner.len() - idx - 1].as_ref()
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn index_pass() {
        let mut stack = Stack::new();

        for i in 0..10 {
            stack.push(i);
        }

        for i in 0..10 {
            assert_eq!(stack[i], 9 - i);
        }
    }

    #[test]
    #[should_panic]
    fn index_fail() {
        let mut stack = Stack::new();
        for i in 0..10 {
            stack.push(i);
        }

        let _ = stack[10];
    }

    #[test]
    fn capture_pass() {
        let mut stack = Stack::new();

        for i in 0..10 {
            stack.push(i);
        }

        let captured = stack.capture(5);

        for i in 0..5 {
            assert_eq!(captured[i], 9 - i);
        }
    }

    #[test]
    #[should_panic]
    fn capture_fail() {
        let mut stack = Stack::new();

        for i in 0..10 {
            stack.push(i);
        }

        let captured = stack.capture(5);

        let _ = captured[5];
    }

    #[test]
    fn isolate_pass() {
        let mut stack = Stack::new();

        for i in 0..5 {
            stack.push(i);
        }

        stack.isolate(|stack| {
            for i in 5..10 {
                stack.push(i);
            }
            for i in 0..10 {
                assert_eq!(stack[i], 9 - i);
            }
        });

        assert_eq!(stack.len(), 5);

        for i in 0..5 {
            assert_eq!(stack[i], 4 - i);
        }
    }
}
