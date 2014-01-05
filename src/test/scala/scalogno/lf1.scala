package scalogno

import scala.language.reflectiveCalls // using new { .. } below

trait Lf1 extends Base with Engine {
  trait LF
  def lf(s: Exp[LF], x: Exp[LF]): Exp[LF] = term("lf", List(s, x))
  def checktp(x: Exp[LF], y: Exp[LF]) = { x === lf(fresh,y); x }

  def dprintln(s:Any) = println(s)

  var instances: Map[String, List[(String,Term)]] = Map.empty withDefaultValue Nil
  def key(a: Atom) = { val s = a.toString; val i = s.indexOf("("); if (i < 0) s else s.substring(0,i) }

  abstract class Term {
    type Self <: Term
    def --(s: String,xs:List[Atom] = Nil): Self = { 
      val x = last
      val k = key(x)
      val r = this.apply(s,xs)
      dprintln(s"register $x $k $s $r")
      instances += (k -> (instances(k) :+ (s,r)))
      r
    }
    def apply(s: String,xs:List[Atom] = Nil): Self
    def *=>:(a: Atom) = a.apply{ _ => this}.asInstanceOf[For[Self]]
    def last: Atom
  }
  case class Atom(lv: Exp[LF]) extends Term {
    type Self = Atom
    def apply(s: String,xs:List[Atom]) = Atom(lf(term(s,xs.map(_.lv)),lv))
    def apply[B<:Term](f: Atom => B) = For[B](this,f)
    def last: Atom = this
    def in[T](f: Atom => T): T = f(this)
    def typed(u: Atom) = { checktp(lv,u.lv); this }
    def ===(u: Atom) = lv === u.lv
    override def toString = extractStr(lv)
  }
  case class For[B<:Term](u: Atom, f: Atom => B) extends Term {
    type Self = For[B#Self]
    def apply(s: String,xs:List[Atom]) = For(u, x => f(x)(s,xs:+x))
    def apply(x:Atom): B = f(x.typed(u))
    def last: Atom = f(%).last
    override def toString = { val z = %.typed(u); z + " => " + f(z) }
  }
  object Term {
    def unapply(x: Exp[LF]) = Some(Atom(x))
  }
  def % = Atom(fresh)


  object typ extends Atom(term[LF]("type", Nil))

  object any {
    def apply[A<:Term](f: Atom => A) = new {
      def apply(): A = f(%)
      def apply(s: String): () => A#Self = () => apply()(s)
      def --(s: String) = For(%,f) -- s
    }
    def apply[A<:Term](f: (Atom,Atom) => A) = new {
      def apply(): A = f(%,%)
      def apply(s: String): () => A#Self = () => apply()(s)
      def --(s: String) = For(%,x => For(%,y => f(x,y))) -- s
    }
    def apply[A<:Term](f: (Atom,Atom,Atom) => A) = new {
      def apply(): A = f(%,%,%)
      def apply(s: String): () => A#Self = () => apply()(s)
      def --(s: String) = For(%,x => For(%,y => For(%,z => f(x,y,z)))) -- s
    }
    def apply[A<:Term](f: (Atom,Atom,Atom,Atom) => A) = new {
      def apply(): A = f(%,%,%,%)
      def apply(s: String): () => A#Self = () => apply()(s)
      def --(s: String): () => A#Self = () => apply() --s
    }
  }


  def searchRule(t: Term, q: Atom): Rel = t match {
    case a @ Atom(lv) => q === a
    case For(u,f) => %.in { z => searchRule(f(z),q) && search(u,z) }
  }

  def search(t: Atom, q: Atom): Rel = instances(key(t)).foldLeft(No:Rel) {
    case (r,(s,t)) => r || {
      dprintln("search "+t+": "+q)
      dprintln("rule "+s+" = "+t)
      searchRule(t,q)
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
    a === add_z(%) ||
    %.in { a1 => a===add_s(%)(%)(%)(a1) && searchAdd(a1) }
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

  test("3 first nats /b") {
    expectResult(List("z", "s(z)", "s(s(z))")) {
      runN[LF](3) {
        case Term(q) =>
          search(nat,q)
      }
    }
  }
  test("5 first additions (concrete) /b") {
    expectResult(List(
      "add(z,z,z)", 
      "add(z,s(z),s(z))", 
      "add(z,s(s(z)),s(s(z)))", 
      "add(z,s(s(s(z))),s(s(s(z))))", 
      "add(z,s(s(s(s(z)))),s(s(s(s(z)))))"
    )) {
      runN[LF](5) {
        case Term(q) =>
          search(add(%)(%)(%), %.typed(q))
      }
    }
  }

}

