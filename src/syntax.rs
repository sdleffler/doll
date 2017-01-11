use std::cmp;
use std::fmt::Debug;
use std::rc::Rc;
use std::result;


use stack::Stack;


#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InfTerm<I> {
    Ann(Rc<ChkTerm<I>>, Rc<ChkTerm<I>>),
    Star,
    Pi(Rc<ChkTerm<I>>, Rc<ChkTerm<I>>),
    Bound(usize),
    Free(Name<I>),
    App(Rc<InfTerm<I>>, Rc<ChkTerm<I>>),
}

pub use self::InfTerm::*;


#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ChkTerm<I> {
    Inf(Rc<InfTerm<I>>),
    Lam(Rc<ChkTerm<I>>),
}

pub use self::ChkTerm::*;


#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Name<I> {
    Global(I),
    Local(usize),
    Quote(usize),
}

pub use self::Name::*;


#[derive(Debug, Clone, PartialEq)]
pub enum Value<I> {
    VLam(Closure<I>),
    VStar,
    VPi(Rc<Value<I>>, Closure<I>),
    VNeutral(Neutral<I>),
}

pub use self::Value::*;


type Env<I> = Stack<Value<I>>;
type Ctx<I> = Stack<(Name<I>, Rc<Value<I>>)>;
type Result<T> = result::Result<T, String>;


#[derive(Debug, Clone, PartialEq)]
pub struct Closure<I> {
    env: Rc<Env<I>>,
    body: Rc<ChkTerm<I>>,
}


impl<I: Debug + Clone + PartialEq> Closure<I> {
    fn eval(&self, arg: Rc<Value<I>>) -> Rc<Value<I>> {
        let mut env = self.env.as_ref().clone().cons_shared(arg);
        self.body.eval(&mut env)
    }
}


#[derive(Debug, Clone, PartialEq)]
pub enum Neutral<I> {
    NFree(Name<I>),
    NApp(Box<Neutral<I>>, Rc<Value<I>>),
}

pub use self::Neutral::*;


impl<I: Debug + Clone + PartialEq> Value<I> {
    fn quote(&self, i: usize) -> Rc<ChkTerm<I>> {
        match *self {
            VLam(ref closure) => {
                Rc::new(Lam(closure.eval(Rc::new(VNeutral(NFree(Quote(i)))))
                    .quote(i + 1)))
            }
            VStar => Rc::new(Inf(Rc::new(Star))),
            VPi(ref bound, ref closure) => {
                Rc::new(Inf(Rc::new(Pi(bound.quote(i),
                                       closure.eval(Rc::new(VNeutral(NFree(Quote(i)))))
                                           .quote(i + 1)))))
            }
            VNeutral(ref n) => Rc::new(Inf(n.quote(i))),
        }
    }
}


impl<I: Debug + Clone + PartialEq> Neutral<I> {
    fn quote(&self, i: usize) -> Rc<InfTerm<I>> {
        match *self {
            NFree(ref x) => x.quote(i),
            NApp(ref n, ref v) => Rc::new(App(n.quote(i), v.quote(i))),
        }
    }
}


impl<I: Clone + PartialEq> Name<I> {
    fn quote(&self, i: usize) -> Rc<InfTerm<I>> {
        match *self {
            Quote(ref k) => Rc::new(Bound(i - k - 1)),
            ref x => Rc::new(Free((*x).clone())),
        }
    }
}


impl<I: Debug + Clone + PartialEq> InfTerm<I> {
    fn depth(&self, i: usize) -> usize {
        match *self {
            Ann(ref e, ref t) => cmp::max(e.depth(i), t.depth(i)),
            Star => 0,
            Pi(ref a, ref b) => cmp::max(a.depth(i), b.depth(i + 1)),
            Free(_) => 0,
            Bound(j) if j > i => j - i,
            Bound(_) => 0,
            App(ref x, ref y) => cmp::max(x.depth(i), y.depth(i)),
        }
    }


    fn eval(&self, env: &mut Env<I>) -> Rc<Value<I>> {
        println!("eval_inf {:?} |- {:?} ~~> ?", env, self);
        match *self {
            Ann(ref e, _) => e.eval(env),
            Star => Rc::new(VStar),
            Pi(ref a, ref b) => {
                Rc::new(VPi(a.eval(env),
                            Closure {
                                env: Rc::new(env.capture(b.depth(0))),
                                body: b.clone(),
                            }))
            }
            Free(ref x) => Rc::new(VNeutral(NFree(x.clone()))),
            Bound(i) => env.share(i),
            App(ref x, ref y) => {
                match *x.eval(env) {
                    VLam(ref closure) => closure.eval(y.eval(env)),
                    VNeutral(ref neutral) => {
                        Rc::new(VNeutral(NApp(Box::new(neutral.clone()), y.eval(env))))
                    }
                    _ => {
                        panic!("Maltyped normal form: Attempted to apply non-lambda, non-neutral \
                                expression to a value.")
                    }
                }
            }
        }
    }


    fn infer_type(&self, i: usize, ctx: &mut Ctx<I>) -> Result<Rc<Value<I>>> {
        println!("infer_type[{}] {:?} |- {:?} : ?", i, ctx, self);
        match *self {
            Ann(ref e, ref t) => {
                let t = {
                    let mut env = Stack::new();
                    t.eval(&mut env)
                };
                e.check_type(i, &t, ctx)?;
                Ok(t)
            }
            Star => Ok(Rc::new(VStar)),
            Pi(ref a, ref b) => {
                a.check_type(i, &VStar, ctx)?;
                let t = {
                    let mut env = Stack::new();
                    b.eval(&mut env)
                };
                ctx.isolate(|mut ctx| {
                        ctx.push((Local(i), t));
                        subst_chk(b, 0, &Rc::new(Free(Local(i)))).check_type(i + 1, &VStar, ctx)
                    })?;
                Ok(Rc::new(VStar))
            }
            Bound(_) => {
                panic!("Error: encountered non-free variable in context {:?} evaluating \
                        expression {:?}",
                       ctx,
                       self)
            }
            Free(ref x) => {
                ctx.lookup(x)
                    .map(Clone::clone)
                    .ok_or_else(|| format!("Variable is not in the local context!"))
                    .clone()
            }
            App(ref a, ref b) => {
                let s = a.infer_type(i, ctx)?;
                match *s {
                    VPi(ref bound, ref closure) => {
                        b.check_type(i, bound, ctx)?;
                        Ok(closure.eval({
                            let mut env = Stack::new();
                            b.eval(&mut env)
                        }))
                    }
                    _ => Err("Illegal application!".to_string()),
                }
            }
        }
    }
}


impl<I: Debug + Clone + PartialEq> ChkTerm<I> {
    fn depth(&self, i: usize) -> usize {
        match *self {
            Inf(ref e) => e.depth(i),
            Lam(ref e) => e.depth(i + 1),
        }
    }

    fn eval(&self, env: &mut Env<I>) -> Rc<Value<I>> {
        println!("eval_chk {:?} |- {:?} ~~> ?", env, self);
        match *self {
            Inf(ref e) => e.eval(env),
            Lam(ref e) => {
                Rc::new(VLam(Closure {
                    env: Rc::new(env.capture(e.depth(0))),
                    body: e.clone(),
                }))
            }
        }
    }

    fn check_type(&self, i: usize, against: &Value<I>, ctx: &mut Ctx<I>) -> Result<()> {
        println!("check_type[{}] {:?} |- {:?} : {:?}", i, ctx, self, against);
        match *self {
            Inf(ref e) => {
                let inferred = e.infer_type(i, ctx)?;
                if *against.quote(0) == *inferred.quote(0) {
                    Ok(())
                } else {
                    Err(format!("Type mismatch: expected {:?}, but inferred {:?}.",
                                inferred,
                                against))
                }
            }
            Lam(ref e) => {
                match *against {
                    VPi(ref bound, ref closure) => {
                        ctx.isolate(|mut ctx| {
                            ctx.push((Local(i), bound.clone()));
                            subst_chk(e, 0, &Rc::new(Free(Local(i))))
                                .check_type(i + 1,
                                            closure.eval(Rc::new(VNeutral(NFree(Local(i)))))
                                                .as_ref(),
                                            &mut ctx)
                        })
                    }
                    _ => Err("Type mismatch!".to_string()),
                }
            }
        }
    }
}


fn subst_inf<I: Debug + Clone + PartialEq>(this: &Rc<InfTerm<I>>,
                                           i: usize,
                                           inj: &Rc<InfTerm<I>>)
                                           -> Rc<InfTerm<I>> {
    // println!("Infer-term substitution: {:?} for DeBruijn {} in {:?}.",
    //          inj,
    //          i,
    //          this);
    match **this {
        Ann(ref e, ref t) => Rc::new(Ann(subst_chk(e, i, inj), subst_chk(t, i, inj))),
        Star => Rc::new(Star),
        Pi(ref a, ref b) => Rc::new(Pi(subst_chk(a, i, inj), subst_chk(b, i + 1, inj))),
        Bound(ref j) => if &i == j { inj.clone() } else { this.clone() },
        Free(ref x) => Rc::new(Free((*x).clone())),
        App(ref x, ref y) => Rc::new(App(subst_inf(x, i, inj), subst_chk(y, i, inj))),
    }
}


fn subst_chk<I: Debug + Clone + PartialEq>(this: &Rc<ChkTerm<I>>,
                                           i: usize,
                                           inj: &Rc<InfTerm<I>>)
                                           -> Rc<ChkTerm<I>> {
    // println!("Checked-term substitution: {:?} for DeBruijn {} in {:?}.",
    //          inj,
    //          i,
    //          this);
    match **this {
        Inf(ref e) => Rc::new(Inf(subst_inf(e, i, inj))),
        Lam(ref e) => Rc::new(Lam(subst_chk(e, i + 1, inj))),
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    use std::rc::Rc;

    use stack::Stack;

    type TestInfTerm = super::InfTerm<&'static str>;
    type TestChkTerm = super::ChkTerm<&'static str>;
    type TestValue = super::Value<&'static str>;

    fn mk_id() -> Rc<TestInfTerm> {
        let id_lam: TestChkTerm =
            Lam(Rc::new(Lam(Rc::new(Inf(Rc::new(Ann(Rc::new(Inf(Rc::new(Bound(0)))),
                                                    Rc::new(Inf(Rc::new(Bound(1)))))))))));
        let id_ty: TestChkTerm =
            Inf(Rc::new(Pi(Rc::new(Inf(Rc::new(Star))),
                           Rc::new(Inf(Rc::new(Pi(Rc::new(Inf(Rc::new(Bound(0)))),
                                                  Rc::new(Inf(Rc::new(Bound(0)))))))))));
        let id: TestInfTerm = Ann(Rc::new(id_lam), Rc::new(id_ty));

        Rc::new(id)
    }

    #[test]
    fn eval_star() {
        let mut env = Stack::new();
        let term: TestInfTerm = Star;

        let val = term.eval(&mut env);

        assert_eq!(*val, VStar);
    }


    #[test]
    fn eval_id() {
        let mut env = Stack::new();

        let term: Rc<TestInfTerm> = Rc::new(App(Rc::new(App(mk_id(),
                                                            Rc::new(Inf(Rc::new(Star))))),
                                                Rc::new(Inf(Rc::new(Star)))));

        let val = term.eval(&mut env);

        assert_eq!(*val, VStar);
    }


    #[test]
    fn typeck_id() {
        let mut env = Stack::new();
        let mut ctx = Stack::new();

        let id: Rc<TestChkTerm> =
            Rc::new(Lam(Rc::new(Lam(Rc::new(Inf(Rc::new(Ann(Rc::new(Inf(Rc::new(Bound(0)))),
                                                            Rc::new(Inf(Rc::new(Bound(1))))))))))));
        let id_ty: Rc<TestValue> =
            Inf(Rc::new(Pi(Rc::new(Inf(Rc::new(Star))),
                           Rc::new(Inf(Rc::new(Pi(Rc::new(Inf(Rc::new(Bound(0)))),
                                                  Rc::new(Inf(Rc::new(Bound(1)))))))))))
                .eval(&mut env);

        id.check_type(0, &id_ty, &mut ctx).unwrap();
    }
}
