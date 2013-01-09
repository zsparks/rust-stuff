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

fn typecheck_and_print (e: @Exp) {
  do iter (@ typecheck (Nil, e))
    |out| { io::println ((**out).to_str()); };
}

fn main () {
  typecheck_and_print (@Lam (@Unit, @Var (0)));
}
