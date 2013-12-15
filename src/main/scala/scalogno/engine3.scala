package scalogno.alt3

trait Base {

  abstract class Rel
  case class Or(x: () => Rel, y: () => Rel) extends Rel
  case class And(x: () => Rel, y: () => Rel) extends Rel
  case class Reg(c: Constraint) extends Rel
  case object Yes extends Rel
  case object No extends Rel


  val Backtrack = new Exception

  def infix_&&(a: => Rel, b: => Rel): Rel = {
    And(() => a, () => b)
  }
  def infix_||(a: => Rel, b: => Rel): Rel = {
    Or(() => a, () => b)
  }
  implicit class RelOps(a: => Rel) {
    def &&(b: => Rel) = infix_&&(a,b)
    def ||(b: => Rel) = infix_||(a,b)
  }

  // dvars

  val dvars0: Map[DVar[_], Any] = Map.empty withDefault (_.default)
  var dvars: Map[DVar[_], Any] = dvars0

  class DVar[T](val default: T) extends (() => T) {
    def apply() = dvar_get(this)
    def :=(v: T) = dvar_set(this, v)
  }

  def DVar[T](v: T): DVar[T] = {
    new DVar[T](v)
  }

  def dvar_set[T](id: DVar[T], v: T): Unit = dvars += id -> v
  def dvar_get[T](id: DVar[T]): T = dvars(id).asInstanceOf[T]
  def dvar_upd[T](id: DVar[T])(f: T => T): Unit = dvars += id -> f(dvar_get(id))


  // constraints

  trait Term[T] {
    val key: String
    def unifyArgs(args1: List[Exp[Any]], args2: List[Exp[Any]]): Rel = 
      ((Yes:Rel) /: (args1,args2).zipped.map((a,b) => (() => a === b)))(_ && _())
    override def toString = key
  }

  abstract class Constraint
  case class IsTerm[T](id: Int, key: Term[T], args: List[Exp[Any]]) extends Constraint
  case class IsEqual(x: Exp[Any], y: Exp[Any]) extends Constraint

  def keys(c: Constraint): List[Int] = c match {
    case IsEqual(Exp(a),Exp(b)) => List(a,b)
    case IsTerm(a, _, _) => List(a)
  }

  def prop(c1: Constraint, c2: Constraint): Rel = (c1,c2) match {
    case (IsTerm(a1, key, args), IsEqual(Exp(a),Exp(b))) if a == a1 =>
      register(IsTerm(b, key, args))
    case (IsEqual(Exp(a),Exp(b)), IsTerm(a1, key, args)) if a == a1 =>
      register(IsTerm(b, key, args))
    case (IsTerm(b1, key, args), IsEqual(Exp(a),Exp(b))) if b == b1 =>
      register(IsTerm(a, key, args))
    case (IsEqual(Exp(a),Exp(b)), IsTerm(b1, key, args)) if b == b1 =>
      register(IsTerm(a, key, args))
    case (IsTerm(a1, key1, args1), IsTerm(a2, key2, args2)) if a1 == a2 =>
      if (key1.key != key2.key || args1.length != args2.length) failc()
      //(args1,args2).zipped foreach ((a,b) => register(IsEqual(a,b)))
      else key1.unifyArgs(args1,args2)
    case _ => Yes
  }

  val cstore = DVar[Set[Constraint]](Set.empty)
  val cindex = DVar[Map[Int, Set[Constraint]]](Map.empty withDefaultValue Set.empty)


  def failc(): Rel = throw Backtrack

  def register(c: Constraint): Rel = {
    val lcstore = cstore()

    if (lcstore.contains(c)) return Yes

    //println("register "+c)

    val lcindex = cindex()

    cstore := lcstore + c
    keys(c) foreach { k => cindex := cindex() + (k -> (cindex()(k) + c)) }

    // use previous index!
    val vs = keys(c) flatMap { k => lcindex(k) map { c2 => () => prop(c,c2) }}
    ((Yes:Rel) /: vs)((a,b) => RelOps(a) && b())
  }


  // term api

  case class Exp[+T](id: Int)

  val varCount0: Int = 0
  var varCount: Int = varCount0

  def fresh[T]: Exp[T] = {
    val id = varCount
    varCount += 1
    Exp[T](id)
  }

  def infix_===[T](a: => Exp[T], b: => Exp[T]): Rel = {
    val c = IsEqual(a,b)
    register(c)
//    Yes
  }

  implicit class ExpOps[T](a: Exp[T]) {
    def ===(b: Exp[T]) = infix_===(a,b)
  }

  def term[T](key0: String, args: List[Exp[Any]]): Exp[T] = {
    val e = fresh[T]
    val c = IsTerm(e.id, new Term[T] { val key = key0 }, args)
    register(c)
    e
  }

  def exists[T](f: Exp[T] => Rel): Rel = {
    f(fresh[T])
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
}

trait Engine extends Base {
  val DEPTH_MAX: Int = 4000
  def run[T](f: Exp[T] => Rel): Seq[String] = runN(Int.MaxValue)(f)
  def runN[T](max: Int)(f: Exp[T] => Rel): Seq[String] = {
    var d: Int = 0
    def printd(x: Any) = println(" "*d+x)

    def rec(e: () => Rel)(f: () => Unit): Unit = {
      if (d == DEPTH_MAX) {
        println("ABORT depth "+d)
        return
      }
      val d1 = d
      val dvars1 = dvars
      try {
        d += 1
        e() match {
          case Or(a,b) =>
            rec(a)(f)
            rec(b)(f)
          case And(a,b) =>
            rec(a) { () =>
              rec(b)(f)
            }
          case Yes =>
            f()
          case No =>
            throw Backtrack
        }
      } catch {
        case Backtrack => // OK
      } finally {
        dvars = dvars1
        d = d1
      }
    }

    val varCount1 = varCount
    val Done = new Exception
    var rn = 0
    val res = new scala.collection.mutable.ListBuffer[String]()
    try {
      val q = fresh[T]
      rec(() => f(q)){() =>
        //println(extractStr(q))
        res += extractStr(q)
        rn += 1
        if (rn>=max) {
          throw Done
        }
      }
    } catch {
      case Done => // OK
    } finally {
      varCount = varCount1
    }

    res.toList
  }

  def dump(out: java.io.PrintWriter)(x: Exp[Any]): Unit = {
    val idx = cstore() groupBy { case IsTerm(id, _ , _) => id case _ => -1 }
    val stack = new scala.collection.mutable.BitSet(varCount)
    val stack2 = new scala.collection.mutable.BitSet(varCount)
    var seenVars: Map[Int,Int] = Map.empty
    def canon(x: Exp[Any]): String = {
      val id = (Set(x.id) ++ (cstore() collect {
        case IsEqual(`x`,y) if y.id < x.id => y.id
        case IsEqual(y,`x`) if y.id < x.id => y.id
      })).min
      val mid = seenVars.get(id) match {
        case None => val mid = seenVars.size; seenVars = seenVars.updated(id, mid); mid
        case Some(mid) => mid
      }
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
        if (key.key == "lf") {
          rec(args.head)
          if (!idx.contains(args.head.id)) { // XXX problem not here: lf(_,_) pattern is not asserted!
            out.print(":")
            rec(args.tail.head)
          }
          if (stack2.contains(id))
            out.print("=r"+id)
          stack -= id
          stack2 -= id
          return
        }

        out.print(key.key)
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

