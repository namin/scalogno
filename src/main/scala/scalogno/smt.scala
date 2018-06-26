package scalogno

trait Smt extends InjectBase with Engine {
  var smt: Exe = _
  def smt_init() = {
    smt = new Exe("cvc4 --interactive --lang smt")
    smt.skipLines(24)
    smt.write("(set-logic ALL_SUPPORTED)")
  }
  def wrap_init[A](a: => A): A = {
    smt_init()
    try {
      return a
    } finally {
      smt.close()
    }
  }
  override def run[T](f: Exp[T] => Rel): Seq[String] =
    wrap_init(super.run(f))
  override def runN[T](max: Int)(f: Exp[T] => Rel): Seq[String] =
    wrap_init(super.runN(max)(f))

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
  def addVar(id: Int) = {
    smt.write(s"(declare-const x$id Int)")
  }
  def check_sat(a: P[Unit]): String = {
    smt.write("(push)")
    val r = a.toString
    smt.write(r)
    smt.write("(check-sat)")
    smt.readLine()
  }
  def check(a: P[Unit])(): Rel = {
    check_sat(a) match {
      case "sat" => {
        val ms = getModel()
        ms.foreach(register)
        Yes ||
          zAssert(P("or", ms.map{e => P("not", List(P("=", List(A(e.x), A(e.y)))))}))
      }
      case "unsat" => {
        smt.write("(pop)")
        No
      }
    }
  }
  def zAssert(p: P[Boolean]): Rel = new Rel {
    def exec(call: Exec)(k: Cont): Unit = {
      call(check(P("assert", List(p))))(k)
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
    def +(b: Z[Int]): Z[Int] = P("+", List(a, b))
  }

  def getModel(): List[IsEqual] = {
    val s = smt.readSExp()
    val p = raw"\(define-fun x([0-9]+) \(\) Int ([0-9]+)\)".r
    val cs = (for (m <- p.findAllMatchIn(s)) yield {
      val id = m.group(1).toInt
      val v = m.group(2).toInt
      val e = IsEqual(Exp(id), v)
      e
    }).toList
    cs
  }
}

class Exe(command: String) {

  import scala.sys.process._
  import scala.io._
  import java.io._
  import scala.concurrent._

  val inputStream = new SyncVar[OutputStream]
  val outputStream = new SyncVar[BufferedReader]

  val process = Process(command).run(
    new ProcessIO(
      stdin => inputStream.put(stdin),
      stdout => outputStream.put(new BufferedReader(new InputStreamReader(stdout))),
      stderr => Source.fromInputStream(stderr).getLines.foreach(println)));

  def skipLines(n: Int) = {
    (0 until n).foreach{_ => readLine()}
  }

  def readLine(): String = synchronized {
    outputStream.get.readLine()
  }

  def readSExp(): String = {
    var sb = new StringBuffer()
    var pl = 0
    var pr = 0
    def processLine() = {
      val line = readLine()
      pl += line.count(_ == '(')
      pr += line.count(_ == ')')
      sb.append(line)
    }
    var first = true;
    while (first || (pr == pr)) {
      processLine()
      first = false
    }
    sb.toString
  }

  def write(s: String): Unit = synchronized {
    inputStream.get.write((s + "\n").getBytes)
    inputStream.get.flush()
  }

  def close(): Unit = {
    inputStream.get.close
    outputStream.get.close
  }
}

object Play extends Smt
