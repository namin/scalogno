package scalogno

/**
 * Sources:
 * - Embedding Prolog in Haskell by JM Spivey, S Seres (1999)
 * - https://github.com/miniKanren/simple-miniKanren
 */
trait Core {
  type S[T] = Seq[T]
  type Predicate = Answer => S[Answer]
  type Answer = (Subst,Int)
  type Subst = List[(Var,Term)]
  type Term = Any

  def infix_*|*(p: Predicate, q: Predicate): Predicate =
    x => p(x) ++ q(x)

  def infix_*&*(p: Predicate, q: Predicate): Predicate =
    p(_).flatMap(q)

  def yes: Predicate =
    x => List(x)

  def no: Predicate =
    x => Nil

  def infix_ext(s: Subst, x: Var, v: Term): Subst =
    (x, v)::s
  def infix_extCheck(s: Subst, x: Var, v: Term): Option[Subst] =
    if (s.occursCheck(x, v)) None else Some(s.ext(x, v))
  def infix_occursCheck(s: Subst, x: Var, v: Term): Boolean = s.walk(v) match {
    case y@Var(i) => x==y
    case u::us => infix_occursCheck(s, x, u) || infix_occursCheck(s, x, us)
    case _ => false
  }
  def infix_walk(s: Subst, u: Term): Term = u match {
    case x@Var(i) => s.collectFirst{case (y,v) if y==x => infix_walk(s, v)}.getOrElse(u)
    case _ => u
  }
  def infix_walkStar(s: Subst, v: Term): Term = s.walk(v) match {
    case x@Var(i) => x
    case v::vs => infix_walkStar(s, v)::infix_walkStar(s, vs).asInstanceOf[List[_]]
    case v => v
  }
  def infix_reifyS(s: Subst, v: Term): Subst = s.walk(v) match {
    case x@Var(i) => s.ext(x, SVar(s.length))
    case v::vs => infix_reifyS(infix_reifyS(s, v), vs)
    case _ => s
  }
  def infix_reify(s: Subst, w: Term): Term = {
    val v = s.walkStar(w)
    id.reifyS(v).walkStar(v)
  }

  def unify(s: Subst)(t1: Term, t2: Term): Option[Subst] = (s.walk(t1),s.walk(t2)) match {
    case (t1, t2) if t1==t2 => Some(s)
    case (x1@Var(i1), t2) => s.extCheck(x1, t2)
    case (t1, x2@Var(i2)) => s.extCheck(x2, t1)
    case (t1::t1s, t2::t2s) => for (s <- unify(s)(t1, t2); s <- unify(s)(t1s, t2s)) yield s
    case _ => None
  }

  case class Var(n: Int)
  case class SVar(n: Int) {
    override def toString = "_." + n
  }
  def makevar(n: Int): Var = Var(n)
  def id: Subst = Nil

  def infix_*=*(t1: Term, t2: Term): Predicate = {
    case (s,n) => for (s2 <- unify(s)(t1,t2).toList) yield (s2,n)
  }

  def E(p: Term => Predicate): Predicate = {
    case (s,n) => p(makevar(n))(s,n+1)
  }

  def solve(p: Predicate): S[String] =
    p(id,0).map(_.toString)

  def run(p: Term => Predicate): S[Term] = {
    val x = makevar(0)
    for ((s,n) <- p(x)(id, 1)) yield (s.reify(x))
  }
}
