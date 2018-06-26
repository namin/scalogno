package scalogno

import java.io._
import scala.sys.process._
import scala.collection._

trait Smt extends InjectBase with Engine {
  trait Z[+T]
  case class A[+T](x: Exp[T]) extends Z[T] {
    override def toString = {
      val cs = cstore.collect{ case(IsTerm(id, k, _)) if x.id == id => k}.toIterator
      if (cs.hasNext) cs.next else { addVar(x.id); "x"+x.id }
    }
  }
  case class P[+T](s: String, args: List[Z[Any]]) extends Z[T] {
    override def toString = {
      val a = args.mkString(" ")
      s"($s $a)"
    }
  }
  val zs = DVar[List[P[Any]]](Nil)
  val ps = DVar[List[List[IsEqual]]](Nil)
  val used_vars0 = immutable.ListSet[Int]()
  var used_vars: immutable.Set[Int] = used_vars0
  def addVar(id: Int) = used_vars += id
  def state(): List[String] = {
    used_vars = used_vars0
    val r1: List[String] = zs().map(_.toString)
    val r2: List[String] =
      for (cs <- ps();  e <- cs) yield P("assert", List(P("not", List(P("=", List(A(e.x), A(e.y))))))).toString
    used_vars.toList.map({i => s"(declare-const x$i Int)"}) ++ r1 ++ r2
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
    def ==?(b: Z[Int]): Rel = zAssert(P("=", List(a, b)))
    def !=?(b: Z[Int]): Rel = zAssert(P("not", List(P("=", List(a, b)))))
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
  def purge(): Rel = {
    val s = call_cvc4(state() ++ List("(check-sat)","(get-model)","(exit)"))
    val lines = augmentString(s).lines
    lines.next match {
      case "sat" => {
        val cs = getModel(s)

        {cs.foreach(register); Yes} ||
        {ps := cs::ps(); purge()}
      }
      case "unsat" => No
    }
  }
  def getModel(s: String): List[IsEqual] = {
    val p = raw"\(define-fun x([0-9]+) \(\) Int ([0-9]+)\)".r
    val cs = (for (m <- p.findAllMatchIn(s)) yield {
      val id = m.group(1).toInt
      val v = m.group(2).toInt
      val e = IsEqual(Exp(id), v)
      e
    }).toList
    cs
  }
  def call_cvc4(lines: List[String]): String = {
    val ls = "(set-logic ALL_SUPPORTED)" :: lines
    val out = new PrintWriter(new FileOutputStream("out.smt"))
    for (l <- ls) out.println(l)
    out.close()
    val s: String = ("cvc4 -m --lang smt out.smt").!!
    s.trim()
  }

  override def run[T](f: Exp[T] => Rel): Seq[String] = {
    super.run[T]{e => f(e) && purge()}
  }
  override def runN[T](max: Int)(f: Exp[T] => Rel): Seq[String] = {
    super.runN[T](max){e => f(e) && purge()}
  }
}

object Play extends Smt {

}
