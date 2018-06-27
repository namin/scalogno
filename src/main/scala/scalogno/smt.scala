package scalogno

import scala.collection._

class SmtSolver {
  var smt: Exe = _
  def init() = {
    smt = new Exe("cvc4 -m --interactive --lang smt")
    smt.skipHeader()
    smt.write("(set-logic ALL_SUPPORTED)")
  }
  def add(c: Any): Unit = {} // TODO
  def checkSat(): Boolean = {
    smt.write("(check-sat)")
    smt.readAtom() match {
      case "sat" => true
      case "unsat" => false
      //case debug => println("smt gives "+debug); true
    }
  }
  def push(): Unit = smt.write("(push)")
  def pop(): Unit = smt.write("(pop)")
  def decl(id: Int): Unit = {
    smt.write(s"(declare-const x$id Int)")
  }
  def add(c: String): Unit = smt.write(c)
  def extractModel(f: (Int,Int) => Unit): Unit = {
    smt.write("(get-model)")
    val s = smt.readSExp()
    val p = raw"\(define-fun x([0-9]+) \(\) Int ([0-9]+)\)".r
    for (m <- p.findAllMatchIn(s)) {
      val id = m.group(1).toInt
      val v = m.group(2).toInt
      println(s"$id has $v")
      f(id, v)
    }
  }
}

trait Smt extends Base with InjectBase {
  abstract class Z[+T]
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

  def extractModel(): List[IsEqual] = {
    var cs: List[IsEqual] = Nil
    solver.extractModel({(x,v) =>
      val c = IsEqual(Exp(x),term(v.toString, Nil))
      cs = c::cs
    })
    cs
  }

  val seenvars0: immutable.Set[Int] = immutable.Set.empty
  var seenvars = seenvars0
  def addVar(id: Int) = { seenvars += id }
  def zAssert(p: P[Boolean]): Rel = new Rel {
    def exec(call: Exec)(k: Cont) = {
      seenvars = seenvars0
      val c = P("assert", List(p)).toString
      seenvars.foreach{solver.decl}
      solver.add(c)
      if (solver.checkSat()) {
        val cs = extractModel()
        call{() => cs.foreach(register); Yes}(k)
        call{() => zAssert(P("not", List(P("and", cs.map({e => P("=", List(A(e.x), A(e.y)))})))))}(k)
      } else {
        throw Backtrack
      }
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

  def skipHeader() = synchronized {
    (0 until 24/*brittle magic*/).foreach{_ => readLine()}
  }

  def readLine(): String = synchronized {
    outputStream.get.readLine()
  }

  def readAtom(): String = synchronized {
    readLine().replaceAll("CVC4> ", "")/*brittle magic*/
  }

  def readSExp(): String = synchronized {
    var sb = new StringBuffer()
    var pl = 0
    var pr = 0
    def processLine() = {
      val line = readLine()
      pl += line.count(_ == '(')
      pr += line.count(_ == ')')
      sb.append(line)
      sb.append(" ")
    }
    var first = true;
    while (first || (pl != pr)) {
      processLine()
      first = false
    }
    sb.toString
  }

  def write(s: String): Unit = synchronized {
    println("smt: "+s)
    inputStream.get.write((s + "\n\n").getBytes)
    inputStream.get.flush()
  }

  def close(): Unit = {
    inputStream.get.close
    outputStream.get.close
  }
}

object Play extends Smt with Engine
