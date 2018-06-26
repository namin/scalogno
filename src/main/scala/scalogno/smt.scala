package scalogno

import java.io._
import scala.sys.process._
import scala.collection._

trait Smt extends InjectBase {
  trait Z[+T]
  case class A[+T](x: Exp[T]) extends Z[T] {
    override def toString = {
      val cs = cstore.collect{ case(IsTerm(id, k, _)) if x.id == id => k}.toList
      if (cs.nonEmpty) cs.head else { addVar(x.id); "x"+x.id }
    }
  }
  case class P[+T](s: String, args: List[Z[Any]]) extends Z[T] {
    override def toString = {
      val a = args.mkString(" ")
      s"($s $a)"
    }
  }
  val zs = DVar[List[P[Any]]](Nil)

  val used_vars0 = immutable.ListSet[Int]()
  var used_vars: immutable.Set[Int] = used_vars0
  def addVar(id: Int) = used_vars += id
  def state() = {
    used_vars = used_vars0
    val r = zs().map(_.toString)
    used_vars.toList.map({i => s"(declare-const x$i Int)"}) ++ r
  }
  def zAssert(p: P[Boolean]): Rel = new Rel {
    def exec(call: Exec)(k: Cont): Unit = {
      zs := zs() ++ List(P("assert", List(p)))
      call(check_sat)(k)
    }
  }

  implicit object InjectInt extends Inject[Int] {
    def toTerm(i: Int): Exp[Int] = term(i.toString,Nil)
  }
  implicit def int2ZInt(e: Int): Z[Int] = toZInt(InjectInt.toTerm(e))
  implicit def toZInt(e: Exp[Int]): Z[Int] = A(e)
  implicit def toZIntOps(e: Exp[Int]) = ZIntOps(A(e))
  implicit class ZIntOps(a: Z[Int]) {
    def =?=(b: Z[Int]): Rel = zAssert(P("=", List(a, b)))
    def >(b: Z[Int]): Rel = zAssert(P(">", List(a, b)))
    def -(b: Z[Int]): Z[Int] = P("-", List(a, b))
    def *(b: Z[Int]): Z[Int] = P("*", List(a, b))
  }
  def check_sat(): Rel = {
    val s = call_cvc4(state() ++ List("(check-sat)","(exit)"))
    s match {
      case "sat" => Yes
      case "unsat" => No
    }
  }
  def call_cvc4(lines: List[String]): String = {
    val ls = "(set-logic QF_UFDTLIAFS)" :: lines
    val out = new PrintWriter(new FileOutputStream("out.smt"))
    for (l <- ls) out.println(l)
    out.close()
    val s: String = ("cvc4 -m --lang smt out.smt").!!
    s.trim()
  }
}

object Play extends Smt with Engine {

}
