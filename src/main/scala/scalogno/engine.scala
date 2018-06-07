package scalogno

import scala.collection._

trait Base {
val Backtrack = new Exception

var varCount: Int = 0
def freshId = {
  var id = varCount
  varCount += 1
  id
}

  implicit class RelOps(a: => Rel) {
    def &&(b: => Rel) = infix_&&(a,b)
    def ||(b: => Rel) = infix_||(a,b)
  }
  implicit class ExpOps[T](a: Exp[T]) {
    def ===[U](b: Exp[U]) = infix_===(a,b)
  }

  def exists[T,U](f: (Exp[T],Exp[U]) => Rel): Rel = {
    f(fresh[T],fresh[U])
  }
  def exists[T,U,V](f: (Exp[T],Exp[U],Exp[V]) => Rel): Rel = {
    f(fresh[T],fresh[U],fresh[V])
  }
  def exists[T,U,V,W](f: (Exp[T],Exp[U],Exp[V],Exp[W]) => Rel): Rel = {
    f(fresh[T],fresh[U],fresh[V],fresh[W])
  }
  def exists[T,U,V,W,X](f: (Exp[T],Exp[U],Exp[V],Exp[W],Exp[X]) => Rel): Rel = {
    f(fresh[T],fresh[U],fresh[V],fresh[W],fresh[X])
  }
  def exists[T,U,V,W,X,Y](f: (Exp[T],Exp[U],Exp[V],Exp[W],Exp[X],Exp[Y]) => Rel): Rel = {
    f(fresh[T],fresh[U],fresh[V],fresh[W],fresh[X],fresh[Y])
  }
  def exists[T,U,V,W,X,Y,Z](f: (Exp[T],Exp[U],Exp[V],Exp[W],Exp[X],Exp[Y],Exp[Z]) => Rel): Rel = {
    f(fresh[T],fresh[U],fresh[V],fresh[W],fresh[X],fresh[Y],fresh[Z])
  }

  def DVar[T](default: T): DVar[T] = new DVar(default)

// dynamically scoped variables
var dvars: Map[DVar[_], Any] =
  Map.empty withDefault (_.default)
class DVar[T](val default: T) {
  def apply()  = dvars(this).asInstanceOf[T]
  def :=(v: T) = dvars += this -> v
}

// relations
trait Rel { def exec(call: Exec)(k: Cont): Unit }
type Exec = (() => Rel) => Cont => Unit
type Cont = () => Unit

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

// logic terms
case class Exp[+T](id: Int)
def fresh[T] = Exp(freshId)


def exists[T](f: Exp[T] => Rel): Rel = f(fresh)

def infix_===[T](a: => Exp[T], b: => Exp[T]): Rel = {
  register(IsEqual(a,b)); Yes }

def term[T](key: String, args: List[Exp[Any]]): Exp[T] = {
  val e = fresh[T]; register(IsTerm(e.id, key, args)); e }  

// constraints
abstract class Constraint
case class IsTerm(id: Int, key: String, args: List[Exp[Any]]) 
  extends Constraint
case class IsEqual(x: Exp[Any], y: Exp[Any]) 
  extends Constraint

val cstore = new DVar[Set[Constraint]](Set.empty)
def conflict(cs: Set[Constraint], c: Constraint): Boolean = {
  false // TODO
}
def register(c: Constraint): Unit = {
  val cs = cstore()
  if (cs.contains(c)) return
  if (conflict(cs,c)) throw Backtrack
  else cstore := cs + c
}
}

trait Engine extends Base {
// execution (depth-first)
def run[T](f: Exp[T] => Rel): Seq[String] = {
  def call(e: () => Rel)(k: Cont): Unit = {
    val dvars1 = dvars
    try {
      e().exec(call)(k)
    } catch {
      case Backtrack => // OK
    } finally {
      dvars = dvars1
    }
  }
  val q = fresh[T]
  val res = mutable.ListBuffer[String]()
  call(() => f(q)) { () =>
    res += extractStr(q)
  }
  res.toList
}

def runN[T](max: Int)(f: Exp[T] => Rel): Seq[String] = {
  def call(e: () => Rel)(k: Cont): Unit = {
    val dvars1 = dvars
    try {
      e().exec(call)(k)
    } catch {
      case Backtrack => // OK
    } finally {
      dvars = dvars1
    }
  }
  val q = fresh[T]
  val res = mutable.ListBuffer[String]()
  val Done = new Exception
  try {
  call(() => f(q)) { () =>
    res += extractStr(q)
    if (res.length>=max) throw Done
  }
  } catch { case Done => }
  res.toList
}

  // def extractStr(x: Exp[Any]): String

  def dump(out: java.io.PrintWriter)(x: Exp[Any]): Unit = {
    val idx = cstore() groupBy { case IsTerm(id, _ , _) => id case _ => -1 }
    val stack = new scala.collection.mutable.BitSet(varCount)
    val stack2 = new scala.collection.mutable.BitSet(varCount)
    val seenVars= new scala.collection.mutable.HashMap[Int,Int]
    def canon(x: Exp[Any]): String = {
      val id = (Set(x.id) ++ (cstore() collect {
        case IsEqual(`x`,y) if y.id < x.id => y.id
        case IsEqual(y,`x`) if y.id < x.id => y.id
      })).min
      val mid = seenVars.getOrElseUpdate(id,seenVars.size)
      "x"+mid
    }
    def rec(x: Exp[Any]): Unit = idx.getOrElse(x.id,Set.empty).headOption match {
      case Some(IsTerm(id, key, args)) =>
        assert(id == x.id)
        if (stack.contains(id)) {
          out.print("r"+id) // not doing occurs check during unification, at least catch cycles here
          stack2 += id
          //return
        }
        stack += id
        // hack -- special case. don't print types.
        if (key == "lf") {
          rec(args.head)
          if (!idx.contains(args.head.id)) {
            out.print(":")
            rec(args.tail.head)
          }
          if (stack2.contains(id))
            out.print("=r"+id)
          stack -= id
          stack2 -= id
          return
        }

        out.print(key)
        if (args.nonEmpty) {
          out.print("(")
          rec(args.head)
          args.tail.foreach { a => out.print(","); rec(a) }
          out.print(")")
        }
        if (stack2.contains(id)) {
          out.print("=r"+id)
        }
        stack -= id
        stack2 -= id
      case _ =>
        out.print(canon(x))
    }
    rec(x)
    out.flush
  }

  def extractStr(x: Exp[Any]): String = {
    val out = new java.io.ByteArrayOutputStream
    dump(new java.io.PrintWriter(new java.io.OutputStreamWriter(out)))(x)
    out.toString
  }
}
