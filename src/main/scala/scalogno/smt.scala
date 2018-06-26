package scalogno

import java.io._
import scala.sys.process._
import scala.collection._

trait Smt extends InjectBase with ListBase with Engine {
  def str(e: Exp[Any]): String = {
    val cs = cstore.collect{ case(IsTerm(id, k, xs)) if e.id == id => (k, xs)}.toIterator
    if (cs.hasNext) {
      val (c, xs) = cs.next
      xs match {
        case Nil => c
        case _ => {
          val a = xs.map(str).mkString(" ")
          s"($c $a)"
        }
      }
    } else {
      addVar(e.id)
      "x"+e.id
    }
  }
  def P(s: String, xs: List[Exp[Any]]): Exp[Any] = term(s, xs)
  def lst(e: Exp[Any]): List[Exp[Any]] = {
    val cs = cstore.collect{ case(IsTerm(id, k, xs)) if e.id == id => (k, xs)}.toIterator
    val (c, xs) = cs.next
    c match {
      case "cons" =>
        val List(x, r:Exp[Any]) = xs
        x::lst(r)
      case "nil" =>
        Nil
    }
  }
  val zs = DVar[Exp[List[Any]]](Nil)
  val used_vars0 = immutable.ListSet[Int]()
  var used_vars: immutable.Set[Int] = used_vars0
  def addVar(id: Int) = used_vars += id
  def state(): List[String] = {
    used_vars = used_vars0
    val r: List[String] = lst(zs()).map(str).reverse
    used_vars.toList.map({i => s"(declare-const x$i Int)"}) ++ r
  }
  def zAssert(p: Exp[Any]): Rel = new Rel {
    def exec(call: Exec)(k: Cont): Unit = {
      zs :=  cons(P("assert", List(p)), zs())
      call(check_sat)(k)
    }
  }

  implicit object InjectInt extends Inject[Int] {
    def toTerm(i: Int): Exp[Int] = term(i.toString,Nil)
  }
  implicit class ZIntOps(a: Exp[Any]) {
    def ==?(b: Exp[Any]): Rel = zAssert(P("=", List(a, b)))
    def !=?(b: Exp[Any]): Rel = zAssert(P("not", List(P("=", List(a, b)))))
    def >(b: Exp[Any]): Rel = zAssert(P(">", List(a, b)))
    def -(b: Exp[Any]): Exp[Any] = P("-", List(a, b))
    def *(b: Exp[Any]): Exp[Any] = P("*", List(a, b))
    def +(b: Exp[Any]): Exp[Any] = P("+", List(a, b))
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
        {zs := cons(neg(cs),zs()); purge()}
      }
      case "unsat" => No
    }
  }
  def neg(cs: List[IsEqual]): Exp[Any] = {
    P("assert", List(P("not", List(P("or", cs.map{e => P("=", List(e.x, e.y))})))))
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
