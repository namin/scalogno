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
  def check(a: P[Unit])(): Rel = {
    smt.write("(push)")
    val r = a.toString
    smt.write(r)
    smt.write("(check-sat)")
    smt.readLine() match {
      case "sat" => {
        Yes
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

  def write(s: String): Unit = synchronized {
    inputStream.get.write((s + "\n").getBytes)
  }

  def close(): Unit = {
    inputStream.get.close
    outputStream.get.close
  }
}

object Play extends Smt
