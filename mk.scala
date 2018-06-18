// code from The Reasoned Schemer, 2nd Edition:
// https://github.com/TheReasonedSchemer2ndEd/CodeFromTheReasonedSchemer2ndEd/blob/master/trs2-impl.scm

trait MicroKanren {
  class Term[+T]
  class Var[+T](x: String) extends Term[T] // no case class for reference equality!
  case class Atom[+T](s: String) extends Term[T]
  case class Fun[+T](s: String, vs: List[Term[Any]]) extends Term[T]
  type Subst = Map[Var[Any],Term[Any]]
  def walk(v: Term[Any], s: Subst): Term[Any] = {
    v match {
      case v:Var[Any] => s.get(v) match {
        case Some(v) => walk(v, s)
        case None => v
      }
      case v => v
    }
  }

  class Inf
  case object INil extends Inf
  case class ICons(a: Subst, d: Inf) extends Inf
  case class IThunk(f: () => Inf) extends Inf
  type Goal = Subst => Inf

  def ext_s(x: Var[Any], v: Term[Any], s: Subst) = {
    if (occurs(x, v, s)) None
    else Some(s + (x -> v))
  }

  def occurs(x: Var[Any], v: Term[Any], s: Subst): Boolean = {
    walk(v, s) match {
      case v:Var[Any] => v == x
      case Fun(_, vs) =>
        vs.exists{v => occurs(x, v, s)}
      case v => false
    }
  }

  def unify(u: Term[Any], v: Term[Any], s: Subst): Option[Subst] = {
    (walk(u, s), walk(v, s)) match {
      case (u, v) if u==v => Some(s)
      case (u:Var[Any],v) => ext_s(u, v, s)
      case (u,v:Var[Any]) => ext_s(v, u, s)
      case (Fun(ut, us), Fun(vt, vs)) if ut==vt =>
        unify_ls(us, vs, s)
      case _ => None
    }
  }

  def unify_ls(us: List[Term[Any]], vs: List[Term[Any]], s: Subst): Option[Subst] = {
    (us, vs) match {
      case (Nil, Nil) => Some(s)
      case (u::us, v::vs) =>
        unify(u, v, s).flatMap{s =>
          unify_ls(us, vs, s)
        }
      case _ => None
    }
  }

  def infix_===[T](u: Term[T], v: Term[T]): Goal = { s =>
    unify(u, v, s) match {
      case Some(s) => ICons(s, INil)
      case None => INil
    }
  }
  implicit class TermEq[T](u: Term[T]) {
    def ===(v: Term[T]) = infix_===(u, v)
  }

  def succeed: Goal = { s => ICons(s, INil) }
  def fail: Goal = { s => INil }

  def disj2(g1: Goal, g2: Goal): Goal = { s =>
    append_inf(g1(s), g2(s))
  }
  implicit class GoalDisj(g1: Goal) {
    def ||(g2: Goal) = disj2(g1, g2)
  }

  def append_inf(s_inf: Inf, t_inf: Inf): Inf = {
    s_inf match {
      case INil => t_inf
      case ICons(a, d_inf) =>
        ICons(a, append_inf(d_inf, t_inf))
      case IThunk(f) =>
        IThunk{ () => append_inf(t_inf, f()) }
    }
  }

  def take_inf(n: Option[Int], s_inf: Inf): List[Subst] = {
    (n, s_inf) match {
      case (Some(n), _) if n==0  => Nil
      case (_, INil) => Nil
      case (_, ICons(a, d_inf)) =>
        a::(take_inf(n.map{n => n-1}, d_inf))
      case (_, IThunk(f)) =>
        take_inf(n, f())
    }
  }

  def conj2(g1: Goal, g2: Goal): Goal = { s =>
    append_map_inf(g2, g1(s))
  }
  implicit class GoalConj(g1: Goal) {
    def &&(g2: Goal) = conj2(g1, g2)
  }

  def append_map_inf(g: Goal, s_inf: Inf): Inf = {
    s_inf match {
      case INil => INil
      case ICons(a, d_inf) =>
        append_inf(g(a), append_map_inf(g, d_inf))
      case IThunk(f) =>
        IThunk{ () => append_map_inf(g, f()) }
    }
  }

  def call_fresh[T](name: String, f: Var[T] => Goal) =
    f(new Var(name))

  def reify_name(n: Int) = "_" + n.toString

  def walk_star(v: Term[Any], s: Subst): Term[Any] = {
    walk(v, s) match {
      case v:Var[Any] => v
      case Fun(t, vs) =>
        Fun(t, vs.map{v => walk_star(v, s)})
      case v => v
    }
  }

  def reify_s(v: Term[Any], r: Subst) = {
    walk(v, r) match {
      case v:Var[Any] =>
        val n = r.size
        val rn = reify_name(n)
        r + (v -> Atom(rn))
      case Fun(t, vs) =>
        reify_ls(vs, r)
      case _ => r
    }
  }

  def reify_ls(vs: List[Term[Any]], r: Subst): Subst = {
    vs match {
      case Nil => r
      case (v::vs) =>
        reify_ls(vs, reify_s(v, r))
    }
  }

  def reify(v: Term[Any]) = { s: Subst =>
    val v2 = walk_star(v, s)
    val r = reify_s(v2, Map.empty)
    walk_star(v2, r)
  }

  def run_goal(n: Option[Int], g: Goal) =
    take_inf(n, g(Map.empty))

  def disj(gs: Goal*): Goal = {
    disj_ls(gs.toList)
  }
  def disj_ls(gs: List[Goal]): Goal = {
    gs match {
      case Nil => fail
      case g::gs => disj2(g, disj_ls(gs))
    }
  }

  def conj(gs: Goal*): Goal = {
    conj_ls(gs.toList)
  }
  def conj_ls(gs: List[Goal]): Goal = {
    gs match {
      case Nil => succeed
      case g::gs => conj(g, conj_ls(gs))
    }
  }

  def rel(g: => Goal): Goal = { s =>
    IThunk{ () => g(s) }
  }

  def run[T](n: Option[Int])(f: Var[T] => Goal) = {
    val q = new Var("q")
    run_goal(n, f(q)).map(reify(q))
  }
  def runA[T](f: Var[T] => Goal) = run(None)(f)
  def runN[T](n: Int)(f: Var[T] => Goal) = run(Some(n))(f)
  def run1[T](f: Var[T] => Goal) = runN(1)(f)

  def nil = Atom("nil")
  def cons[T](v: Term[T], vs: Term[List[T]]) = Fun[List[T]]("cons", List(v,vs))
  def pair[A,B](a: Term[A], b: Term[B]) = Fun[(A,B)]("pair", List(a, b))
  def lift[T](xs: List[Term[T]]): Term[List[T]] = xs match {
    case Nil => nil
    case x::xs => cons(x, lift(xs))
  }
  def fresh[T](f: Var[T] => Goal) = call_fresh("x", f)
  def freshN[T](n: Int)(f: List[Var[T]] => Goal) =
    f((0 until n).map{_ => new Var("x")}.toList)

  def lst[T](xs: Term[T]*) = lift(xs.toList)
  def i(n: Int) = Atom[Int](n.toString)
}

object mk extends MicroKanren

object tests extends App {
  import mk._

  assert(run1[Any]{q => succeed} == List(Atom("_0")))
  assert(runA[Any]{q => succeed} == List(Atom("_0")))

  assert(run1[Any]{q => freshN(2){ case List(x, y) => q === pair(x,y) }} == List(Fun("pair",List(Atom("_0"), Atom("_1")))))
  assert(runA[Any]{q => fresh[Any]{x => q === pair(x, x)}} == List(Fun("pair",List(Atom("_0"), Atom("_0")))))
  assert(runA[Any]{q => fresh[Any]{x => fresh[Any]{y => q === pair(x, y)}}} == List(Fun("pair",List(Atom("_0"), Atom("_1")))))
  assert(runA[Any]{q => freshN[Any](2){case List(x, y) => q === pair(x,y)}} == List(Fun("pair",List(Atom("_0"), Atom("_1")))))

  assert(runA[Any]{q => succeed || fail} == List(Atom("_0")))
  def loopo(): Goal = rel{fail || loopo()}
  assert(run1[Any]{q => succeed || loopo()} == List(Atom("_0")))

  assert(run1[Any]{q => q === i(1) || q === i(2)} == List(Atom("1")))
  assert(runA[Any]{q => q === i(1) || q === i(2)} == List(Atom("1"), Atom("2")))

  def appendo[T](xs: Term[List[T]], ys: Term[List[T]], zs: Term[List[T]]): Goal = rel{
    (xs === nil && ys === zs) ||
    fresh[T]{ first => freshN[List[T]](2){ case List(rest, rs) =>
      cons(first, rest) === xs &&
      cons(first, rs) === zs &&
      appendo(rest, ys, rs)
    }}
  }

  assert(runA[List[Int]]{q => appendo(lst(i(1),i(2)), lst(i(3),i(4),i(5)), q)} == List(lst(i(1),i(2),i(3),i(4),i(5))))
  assert(runA[Any]{q => freshN[List[Int]](2){ case List(x,y) => q === cons(x,y) && appendo(x, y, lst(i(1),i(2),i(3),i(4),i(5))) }} == List(
    cons(nil, lst(i(1),i(2),i(3),i(4),i(5))),
    cons(lst(i(1)), lst(i(2),i(3),i(4),i(5))),
    cons(lst(i(1),i(2)), lst(i(3),i(4),i(5))),
    cons(lst(i(1),i(2),i(3)), lst(i(4),i(5))),
    cons(lst(i(1),i(2),i(3),i(4)), lst(i(5))),
    cons(lst(i(1),i(2),i(3),i(4),i(5)), nil)
  ))
}
