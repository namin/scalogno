package scalogno

import scala.language.higherKinds

/**
 * Sources:
 * - microKanren
 */
trait MicroKanren {
  type Exp = Any
  case class Var(id: Int)

  type Goal = State => S[State]
  type State = (Subst, Int)
  type Subst = List[(Var,Exp)]

  def exists(f: Var => Goal): Goal = {
    case (a,c) => f(Var(c))(a,c+1)
  }

  def disj(g0: Goal, g1: Goal): Goal = { ac =>
    thunk(mplus(g0(ac), g1(ac)))
  }

  def conj(g0: Goal, g1: Goal): Goal = { ac =>
    thunk(bind(g0(ac), g1))
  }

  def ===(u: Exp, v: Exp): Goal = {
    case (a,c) => unify(u, v, a) match {
      case Some(s) => unit((s,c))
      case None => mzero
    }
  }

  def no: Goal = ===(0,1)
  def yes: Goal = ===(1,1)

  def walk(u: Exp, s: Subst): Exp = u match {
    case x@Var(i) => s.collectFirst{case (y,v) if y==x => walk(v, s)}.getOrElse(u)
    case _ => u
  }

  def ext_s(x: Var, v: Exp, s: Subst): Subst = (x,v)::s

  def unify(u: Exp, v: Exp, s: Subst): Option[Subst] = (walk(u,s),walk(v,s)) match {
    case (u, v) if v==u => Some(s)
    case (u@Var(_), v) => ext_s_check(u, v, s)
    case (u, v@Var(_)) => ext_s_check(v, u, s)
    case (u1::us, v1::vs) => for (s <- unify(u1, v1, s); s <- unify(us, vs, s)) yield s
    case _ => None
  }

  def ext_s_check(x: Var, v: Exp, s: Subst): Option[Subst] = {
    if (occurs_check(x, v, s)) None else Some(ext_s(x, v, s))
  }

  def occurs_check(x: Var, v: Exp, s: Subst): Boolean = walk(v, s) match {
    case v@Var(_) => v==x
    case v::vs => occurs_check(x, v, s) || occurs_check(x, vs, s)
    case _ => false
  }

  def walkStar(w: Exp, s: Subst): Exp = walk(w, s) match {
    case v@Var(_) => v
    case v::vs => walkStar(v, s)::walkStar(vs, s).asInstanceOf[List[_]]
    case v => v
  }

  case class SVar(id: Int) {
    override def toString = "_." + id
  }

  def size_s(s: Subst): Int = s.length

  def reify_s(v: Exp, s: Subst): Subst = walk(v, s) match {
    case v@Var(_) => ext_s(v, SVar(size_s(s)), s)
    case v::vs => reify_s(vs, reify_s(v, s))
    case _ => s
  }

  val emptyState: State = (Nil, 0)
  val var0: Var = Var(0)
  val idSubst: Subst = Nil
  def reify(s: Subst, w: Exp): Exp = {
    val v = walkStar(w, s)
    walkStar(v, reify_s(v, idSubst))
  }
  def reify1st: State => Exp = {
    case (s,n) => reify(s, var0)
  }

  def pull[A](ac_inf: S[A]): Stream[A] = ac_inf match {
    case Zero => Stream.empty
    case Thunk(f) => pull(f())
    case Choice(ac, f) => Stream.cons(ac, pull(f()))
  }

  def run(g: Goal): Stream[Exp] = pull(g(emptyState)).map(reify1st)

  def mplus(ac_inf: S[State], f: => S[State]): S[State] = ac_inf match {
    case Zero => f
    case Thunk(f2) => thunk(mplus(f, f2()))
    case Choice(ac1, f2) => choice(ac1, mplus(f, f2()))
  }

  def bind(ac_inf: S[State], g: Goal): S[State] = ac_inf match {
    case Zero => mzero
    case Thunk(f) => thunk(bind(f(), g))
    case Choice(ac1, f) => mplus(g(ac1), thunk(bind(f(), g)))
  }

  sealed abstract class S[+A]
  case object Zero extends S[Nothing]
  case class Thunk[A](f: () => S[A]) extends S[A]
  case class Choice[A](ac: A, f: () => S[A]) extends S[A]
  def mzero: S[State] = Zero
  def unit(ac: State): S[State] = choice(ac, mzero)
  def choice(ac: State, f: => S[State]): S[State] = Choice(ac, () => f)
  def thunk(f: => S[State]) = Thunk(() => f)
}
