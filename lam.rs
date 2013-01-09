extern mod std;
use std::list::*;
use core::option::*;
use core::to_str::*;

enum Tp {
  Unit
, Arr (@Tp, @Tp)
}

impl Tp: Eq {

  pure fn eq (other: &Tp) -> bool {
    match (self, *other) {
      (Unit, Unit) => true
    , (Arr (@t1a, t2a), Arr (@t1b, t2b)) => t1a.eq (t2a) && t1b.eq (t2b)
    , _ => false
    }
  }

  pure fn ne (other: &Tp) -> bool {
    ! (self.eq (other))
  }

}

impl Tp: ToStr {

  pure fn to_str() -> ~str {
    match self {
      Unit => ~"Unit"
    , Arr (@t1, @t2) =>
        str::append (t1.to_str(), str::append (~" -> ", t2.to_str()))
    }
  }

}

impl Exp: ToStr {

  pure fn to_str() -> ~str {
    match self {
      Triv => ~"Triv"
    , App (@e1, @e2) =>
        str::concat ([e1.to_str(), ~" ", e2.to_str()])
    , Lam (@t, @body) => 
        str::concat ([~"Lambda ", t.to_str(), ~" (", body.to_str(), ~")"])
    , Var (i) => i.to_str()
    }
  }

}

enum Exp {
  Triv
, Lam (@Tp, @Exp)
, App (@Exp, @Exp)
, Var (int)
}

pure fn nth<T: Copy> (l: List<T>, n: int) -> Option<T> {
  match l {
    Nil => None
  , Cons (t, @l) => if (n == 0) { Some (t) } else { nth (l, n - 1) }
  }
}

pure fn typecheck (ctx: List<@Tp>, exp: @Exp) -> Option<@Tp> {
    match *exp {
    Triv => Some (@Unit)

  , Lam (t, e) =>
      do chain (typecheck (Cons (t, @ctx), e))
        |tout| { Some (@Arr (t, tout)) }

  , App (e1, e2) =>
      match typecheck (ctx, e1) {
        Some (@Arr (@t, tout)) =>
          do chain (typecheck (ctx, e2))
            |t2| {
              if (t.eq (t2)) {
                Some (tout)
              }
              else {
                None
              }
            }
      , _ => None
      }

  , Var (i) => nth (ctx, i)
  }
}

pure fn value (e: @Exp) -> bool {
  match *e {
    Triv => true
  , Lam (*) => true
  , _ => false
  }
}

pure fn subst_i (e: @Exp, ehole: @Exp, i: int) -> @Exp {
  match *ehole {
    Var (j) if j == i => e
  , Var (j) => @ Var (j - 1)
  , App (e1, e2) => @ App (subst_i (e, e1, i), subst_i (e, e2, i))
  , Lam (t, body) => @ Lam (t, subst_i (e, body, i + 1))
  , Triv => ehole
  }
}

pure fn subst (e: @Exp, ehole: @Exp) -> @Exp {
  subst_i (e, ehole, 0)
}

pure fn step (e: @Exp) -> Option<@Exp> {
  match *e {
    App (e1 @ @Lam (_, body), e2) =>
      if value (e2) {
        Some (subst (e2, body))
      }
      else {
        do chain (step (e2))
          |e2out| { Some (@App (e1, e2out)) }
      }
  , _ => None
  }
}

pure fn eval (e: @Exp) -> Option<@Exp> {
  if value (e) {
    Some (e)
  }
  else {
    chain (step (e), eval)
  }

}

fn typecheck_and_print (e: @Exp) {
  do iter (@ typecheck (Nil, e))
    |out| { io::println ((**out).to_str()); };
}

fn eval_and_print (e: @Exp) {
  match (eval (e)) {
    None => io::println ("Failure.")
  , Some (v) => io::println (v.to_str())
  }
}


fn main () {
  let id_exp : @Exp = @Lam (@Unit, @Var (0));
  let id_app_triv : @Exp = @App (id_exp, @Triv);
  typecheck_and_print (id_exp);
  typecheck_and_print (id_app_triv);
  eval_and_print (id_app_triv);
}
