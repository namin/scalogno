import scala.collection._

abstract class ScalognoBase {
val solver: Solver

type Goal = () => Rel

trait Rel { def exec(call: Exec)(k: Cont): Unit }
type Exec = Goal => Cont => Unit
type Cont = () => Unit

val Backtrack = new Exception

val Yes = new Rel { 
  def exec(call: Exec)(k: Cont) = k() }
val No = new Rel { 
  def exec(call: Exec)(k: Cont) = throw Backtrack }
def infix_&&(a: => Rel, b: => Rel): Rel = new Rel {
  def exec(call: Exec)(k: Cont) =
    call(() => a) { () => call(() => b)(k) } }
def infix_||(a: => Rel, b: => Rel): Rel = new Rel {
  def exec(call: Exec)(k: Cont) = {
    call(() => a)(k); call(() => b)(k) }}

def call(g: Goal)(k: Cont): Unit = {
  val restore = solver.push()
  try {
    g().exec(call)(k)
  } catch {
    case Backtrack => // OK
  } finally {
    solver.pop(restore)
  }
}

case class Exp[+T](id: Int)

abstract class Constraint
case class IsTerm(id: Int, key: String, args: List[Exp[Any]])  extends Constraint
case class IsEqual(x: Exp[Any], y: Exp[Any])  extends Constraint

def exists[T](f: Exp[T] => Rel): Rel = f(solver.fresh)
def infix_===[T](a: => Exp[T], b: => Exp[T]): Rel = {
  solver.register(IsEqual(a,b)); Yes }
def term[T](key: String, args: List[Exp[Any]]): Exp[T] = {
  val e = solver.fresh[T];
  solver.register(IsTerm(e.id, key, args)); e }

def runN[T](max: Int)(f: Exp[T] => Rel): Seq[solver.Model] = {
  val q = solver.fresh[T]
  val res = mutable.ListBuffer[solver.Model]()
  val Done = new Exception
  try { call(() => f(q)) { () =>
    res += solver.extractModel(q)
    if (res.length >= max) throw Done
  }} catch { case Done => }
  res.toList
}
def run[T](f: Exp[T] => Rel): Seq[solver.Model] = runN(scala.Int.MaxValue)(f)

abstract class Solver {
  type State
  type FullState = (String, State)
  type Model
  def push(): State
  def pop(restore: State): Unit
  def save(): FullState = {
    ("", push())
  }
  def reset(restore: FullState): Unit = {
    pop(restore._2)
  }
  def fresh[T]: Exp[T]
  def register(c: Constraint): Unit
  def extractModel(x: Exp[Any]): Model

  def init(): Unit = {}
  def cstore: immutable.Set[Constraint]
  def decl(id: Int): Unit = {}
  def add(c: String): Unit = {}
  def checkSat(): Boolean = true

  def varCount: Int
}

class VanillaSolver extends BaseSolver {
  override type State = immutable.Set[Constraint]
  override def push(): State = cstore
  override def pop(restore: State): Unit = { cstore = restore }
}
abstract class BaseSolver extends Solver {
  override type Model = String
  var cstore: immutable.Set[Constraint] = immutable.Set.empty

  var varCount: Int = 0
  def freshId = {
    val id = varCount
    varCount += 1
    id
  }
  override def fresh[T]: Exp[T] = Exp(freshId)

  override def register(c: Constraint): Unit = {
    if (cstore.contains(c)) return
    if (conflict(cstore,c)) throw Backtrack
  }
  def conflict(cs: Set[Constraint], c: Constraint): Boolean = {
  def prop(c1: Constraint, c2: Constraint)(fail: () => Nothing): List[Constraint] = (c1,c2) match {
    case (IsEqual(a1,b1), IsEqual(a2,b2)) if a1 == a2 || a1 == b2 || b1 == a2 || b1 == b2 =>
      List(IsEqual(a1,a2),IsEqual(a1,b2),IsEqual(b1,a2),IsEqual(b1,b2))

    case (IsEqual(Exp(a),Exp(b)), IsTerm(a1, key, args)) if a == a1 =>
      List(IsTerm(b, key, args))
    case (IsTerm(a1, key, args), IsEqual(Exp(a),Exp(b))) if a == a1 =>
      List(IsTerm(b, key, args))
    case (IsEqual(Exp(a),Exp(b)), IsTerm(a1, key, args)) if a == a1 =>
      List(IsTerm(b, key, args))
    case (IsTerm(b1, key, args), IsEqual(Exp(a),Exp(b))) if b == b1 =>
      List(IsTerm(a, key, args))
    case (IsEqual(Exp(a),Exp(b)), IsTerm(b1, key, args)) if b == b1 =>
      List(IsTerm(a, key, args))

    case (IsTerm(a1, key1, args1), IsTerm(a2, key2, args2)) if a1 == a2 =>
      if (key1 != key2 || args1.length != args2.length) fail()
      (args1,args2).zipped map (IsEqual(_,_))
    case _ => Nil
  }

  val fail = () => throw Backtrack

  val cn = cs flatMap { c2 => prop(c, c2)(fail) }
  cstore += c

  cn foreach register
  false
}

  def extractModel(x: Exp[Any]): Model = {
    val cs = cstore.collect{ case(IsTerm(id, k, xs)) if x.id == id => (k,xs)}.toIterator
    if (cs.hasNext) {
      val (k, xs) = cs.next
      xs match {
        case Nil => k
        case _ => "("+k+xs.map(extractModel).mkString(" ")+")"
      }
    } else {
      "x"+x.id
    }
  }
}

  implicit class RelOps(a: => Rel) {
    def &&(b: => Rel) = infix_&&(a,b)
    def ||(b: => Rel) = infix_||(a,b)
  }
  implicit class ExpOps[T](a: Exp[T]) {
    def ===[U](b: Exp[U]) = infix_===(a,b)
  }

class SmtSolver extends VanillaSolver {
  val smt = new SmtEngine()
  override def init(): Unit = {
    smt.init()
  }
  override def push(): State = {
    smt.push()
    super.push()
  }
  override def pop(restore: State): Unit = {
    smt.pop()
    super.pop(restore)
  }
  override def save(): FullState = {
    (smt.save(), super.push())
  }
  override def reset(restore: FullState): Unit = {
    smt.reset(restore._1)
    super.reset(restore)
  }
  override def decl(id: Int): Unit = smt.decl(id)
  override def add(c: String): Unit = smt.add(c)
  override def checkSat(): Boolean =  smt.checkSat()
  override def extractModel(x: Exp[Any]): Model = {
    smt.extractModel({(x,v) =>
      register(IsEqual(Exp(x),term(v.toString, Nil)))
    })
    super.extractModel(x)
  }
}
}

object scalogno extends ScalognoBase {
  override val solver = new VanillaSolver()
}

trait ScalognoSmt extends ScalognoBase {
  abstract class Z[+T]
  case class A[+T](x: Exp[T]) extends Z[T] {
    override def toString = {
      val cs = solver.cstore.collect{ case(IsTerm(id, k, _)) if x.id == id => k}.toIterator
      if (cs.hasNext) cs.next else { addVar(x.id); "x"+x.id }
    }
  }
  case class P[+T](s: String, args: List[Z[Any]]) extends Z[T] {
    override def toString = {
      val a = args.mkString(" ")
      s"($s $a)"
    }
  }

  object InjectInt {
    implicit def toTerm(i: Int): Exp[Int] = term(i.toString,Nil)
  }
  implicit def int2ZInt(e: Int): Z[Int] = toZInt(InjectInt.toTerm(e))
  implicit def toZInt(e: Exp[Int]): Z[Int] = A(e)
  implicit def toZIntOps(e: Exp[Int]) = ZIntOps(A(e))
  implicit class ZIntOps(a: Z[Int]) {
    def ==?(b: Z[Int]): Rel = zAssert(P("=", List(a, b)))
    def !=?(b: Z[Int]): Rel = zAssert(P("not", List(P("=", List(a, b)))))
    def >(b: Z[Int]): Rel = zAssert(P(">", List(a, b)))
    def >=(b: Z[Int]): Rel = zAssert(P(">=", List(a, b)))
    def -(b: Z[Int]): Z[Int] = P("-", List(a, b))
    def *(b: Z[Int]): Z[Int] = P("*", List(a, b))
    def +(b: Z[Int]): Z[Int] = P("+", List(a, b))
  }

  val seenvars0: immutable.Set[Int] = immutable.Set.empty
  var seenvars = seenvars0
  def addVar(id: Int) = { seenvars += id }
  def zAssert(p: P[Boolean]): Rel = {
    seenvars = seenvars0
    val c = P("assert", List(p)).toString
    seenvars.foreach{solver.decl}
    solver.add(c)
    if (!solver.checkSat()) throw Backtrack
    Yes
  }
}

trait ScalognoTabling extends ScalognoSmt {
type Answer = (Exp[Any] => Unit)
case class Call(key: String, goal1: Exp[Any], state1: solver.FullState, k1: Cont) {
  def load(ans: Answer): Unit = {
    solver.reset(state1)
    ans(goal1);
  }
}

val ansTable = new mutable.HashMap[String, mutable.HashMap[String, Answer]]
val contTable = new mutable.HashMap[String, List[Call]]

// save complete call state
def makeCall(goal0: Exp[Any], k: Cont): Call = {
  val key = solver.extractModel(goal0).asInstanceOf[String]
  val cont = Call(key,goal0,solver.save(),k)
  contTable(key) = cont::contTable.getOrElse(key,Nil)
  cont
}

def makeAnswer(g1: Exp[Any]): Answer = {
  val lcstore = solver.cstore
  val lidx = solver.cstore groupBy { case IsTerm(id, _ , _) => id case _ => -1 }

  (g2: Exp[Any]) => {

    val stack = new mutable.BitSet(solver.varCount)
    val seenVars = new mutable.HashMap[Int,Int]
    def copyVar(x: Exp[Any]): Exp[Any] = {
      val id = (Set(x.id) ++ (lcstore collect {
        case IsEqual(`x`,y) if y.id < x.id => y.id
        case IsEqual(y,`x`) if y.id < x.id => y.id
      })).min
      val mid = seenVars.getOrElseUpdate(id,seenVars.size)
      Exp(mid)
    }
    def copyTerm(x: Exp[Any]): Exp[Any] = lidx.getOrElse(x.id,Set.empty).headOption match {
      case Some(IsTerm(id, key, args)) =>
        assert(id == x.id)
        assert(!stack.contains(id), "cyclic terms not handled")
        try {
          stack += id
          term(key, args map copyTerm)
        } finally {
          stack -= id
        }
      case _ =>
        copyVar(x)
    }

    val g1_copy = copyTerm(g1)

    g1_copy === g2
  }
}

def memo(goal0: Exp[Any])(a: => Rel): Rel = new Rel {
  override def exec(rec: Exec)(k: Cont): Unit = {
    def resume(cont: Call, ans: Answer) = rec{ () => cont.load(ans); Yes }(cont.k1)

    val cont = makeCall(goal0, k)
    ansTable.get(cont.key) match {
      case Some(answers) =>
        for (ans <- answers.values) resume(cont, ans)
      case None =>
        val ansMap = new mutable.HashMap[String, Answer]
        ansTable(cont.key) = ansMap
        rec { () =>
          a
        } { () =>
          val ansKey = solver.extractModel(goal0).asInstanceOf[String]
          ansMap.get(ansKey) match {
            case None =>
              val ans = makeAnswer(cont.goal1)
              ansMap(ansKey) = ans
              for (cont1 <- contTable(cont.key).reverse) {
                resume(cont1, ans)
              }
            case Some(_) =>
          }
        }
    }
  }
}
}

object scalogno_smt extends ScalognoSmt {
  override val solver = new SmtSolver()
}

object test {
  import scalogno_smt._
  import InjectInt._

  def faco(n: Exp[Int], o: Exp[Int]): Rel =
    (n >= 0) && (
      (n ==? 0) && (o ==? 1) ||

      exists[Int]{n1 => exists[Int]{r =>
        (n - 1) ==? n1 &&
          (n * r) ==? o &&
        faco(n1, r)
      }}
    )

  def main(args: Array[String]) {
    solver.init()
    assert(run[Any]{q => q === 1 || q === 2} == List("1","2"))
    assert(run[Int]{q => q ==? 1 || q ==? 2} == List("1","2"))
    assert(runN[Int](7){ o => exists[Int]{n => faco(n,o)} } ==
      List("1", "1", "2", "6", "24", "120", "720"))
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

class SmtEngine {
  var smt: Exe = _
  def init() = {
    smt = new Exe("cvc4 -m --interactive --lang smt")
    smt.skipHeader()
    smt.write("(set-logic ALL_SUPPORTED)")
  }
  def checkSat(): Boolean = {
    smt.write("(check-sat)")
    smt.readAtom() match {
      case "sat" => true
      case "unsat" => false
      //case debug => println("smt gives "+debug); true
    }
  }
  var scope = 0
  var lines: List[List[String]] = Nil
  def push(): Unit = {
    scope += 1
    lines = Nil::lines
    smt.write("(push)")
  }
  def pop(): Unit = {
    scopes = scopes.collect{case (k,v) if v < scope => (k,v)}.toMap
    scope -= 1
    lines = lines.tail
    smt.write("(pop)")
  }
  var scopes: Map[Int,Int] = Map.empty
  def decl(id: Int): Unit = {
    scopes.get(id) match {
      case None =>
        add(s"(declare-const x$id Int)")
        scopes += (id -> scope)
      case Some(s) =>
        if (s >= scope) {
          add(s"(declare-const x$id Int)")
          scopes += (id -> scope)
        }
    }
  }
  def add(c: String): Unit = {
    print(scope.toString+" ")
    lines = (c::lines.head)::lines.tail
    smt.write(c)
  }
  var from = "(reset)\n"
  def save(): String = {
    from+lines.reverse.map(_.reverse.mkString("\n")).mkString("\n")
  }
  def reset(x: String): Unit = {
    from = x+"\n"
    smt.write(from)
  }
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
