package scalogno

import scala.language.reflectiveCalls // using new { .. } below

trait Lf1 extends Base with Engine {
  trait LF
  def lf(s: Exp[LF], x: Exp[LF]): Exp[LF] = term("lf", List(s, x))
  def checktp(x: Exp[LF], y: Exp[LF]) = { x === lf(fresh,y); x }

  def dprintln(s:Any) = ()

  abstract class Term {
    type Self <: Term
    def --(s: String,xs:List[Atom] = Nil): Self = this.apply(s,xs)
    def apply(s: String,xs:List[Atom] = Nil): Self
    def *=>:(a: Atom) = a.apply{ _ => this}.asInstanceOf[For[Self]]
  }
  case class Atom(lv: Exp[LF]) extends Term {
    var instances: List[Exp[LF]] = Nil
    type Self = Atom
    def apply(s: String,xs:List[Atom]) = {
      val at = Atom(lf(term(s,xs.map(_.lv)),lv))
      dprintln("at "+extractStr(lv)+" new "+extractStr(at.lv))
      at
    }
    def apply[B<:Term](f: Atom => B) = For[B](this,f)
    def in[T](f: Atom => T): T = f(this)
    def typed(u: Atom) = { checktp(lv,u.lv); this }
    def ===(u: Atom) = lv === u.lv
  }
  case class For[B<:Term](u: Atom, f: Atom => B) extends Term {
    type Self = For[B#Self]
    def apply(s: String,xs:List[Atom]) = {
      dprintln("register fun " + this + " as " + s)
      For(u, x => f(x)(s,xs:+x))
    }
    def apply(x:Atom): B = f(x.typed(u))
  }
  object Term {
    def unapply(x: Exp[LF]) = Some(Atom(x))
  }
  def % = Atom(fresh)


  object typ extends Atom(term[LF]("type", Nil))

  object any {
    def apply[A<:Term](f: Atom => A) = new {
      def apply(): A = f(%)
      def apply(s: String): () => A#Self = {
        dprintln("register any1 " + this + " as " + s)
        () => apply()(s)
      }
      def --(s: String) = this(s)
    }
    def apply[A<:Term](f: (Atom,Atom) => A) = new {
      def apply(): A = f(%,%)
      def apply(s: String): () => A#Self = {
        dprintln("register any2 " + this + " as " + s)
        () => apply()(s)
      }
      def --(s: String) = this(s)
    }
    def apply[A<:Term](f: (Atom,Atom,Atom) => A) = new {
      def apply(): A = f(%,%,%)
      def apply(s: String): () => A#Self = {
        dprintln("register any3 " + this + " as " + s)
        () => apply()(s)
      }
      def --(s: String) = this(s)
    }
    def apply[A<:Term](f: (Atom,Atom,Atom,Atom) => A) = new {
      def apply(): A = f(%,%,%,%)
      def apply(s: String): () => A#Self = {
        dprintln("register any4 " + this + " as " + s)
        () => apply()(s)
      }
      def --(s: String) = this(s)
    }
  }
}

trait Naturals extends Lf1 {
  val nat = typ           -- "nat"
  val z   = nat           -- "z"
  val s   = nat *=>: nat  -- "s"

  val add   = nat *=>: nat *=>: nat *=>: typ -- "add"
  val add_z = any { N =>
    add(z)(N)(N)
  }                                          -- "add_z"
  val add_s = any { (N1,N2,N3) =>
    add(N1)(N2)(N3) *=>:
    add(s(N1))(N2)(s(N3))
  }                                          -- "add_s"

  dprintln("done init")

  def searchNat(n: Atom): Rel = {
    n === z ||
    %.in { m => n===s(m) && searchNat(m) }
  }
  def searchAdd(a: Atom): Rel = {
    a === add_z() ||
    %.in { a1 => a===add_s()(a1) && searchAdd(a1) }
  }
}


import org.scalatest._

class TestNaturals extends FunSuite with Base with Engine with Naturals with ListBase {
  test("3 first nats") {
    expectResult(List("z", "s(z)", "s(s(z))")) {
      runN[LF](3) {
        case Term(q) =>
          searchNat(q.typed(nat))
      }
    }
  }
  test("3 first additions") {
    expectResult(List("add(z,x0:nat,x0:nat)","add(s(z),x0:nat,s(x0:nat))","add(s(s(z)),x0:nat,s(s(x0:nat)))")) {
      runN[LF](3) {
        case Term(q) =>
          searchAdd(%.typed(q))
      }
    }
  }
}

