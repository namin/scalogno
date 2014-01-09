package scalogno

trait Base {
  case class Exp[+T](id: Int)
  val varCount0: Int = 0
  var varCount: Int = varCount0
  def fresh[T]: Exp[T] = {
    val id = varCount
    varCount += 1
    Exp[T](id)
  }
  abstract class Constraint
  case class IsTerm(id: Int, key: String, args: List[Exp[Any]]) extends Constraint
  case class IsEqual(x: Exp[Any], y: Exp[Any]) extends Constraint

  abstract class Cmd
  case class Or(x: () => Rel, y: () => Rel) extends Cmd
  case class And(x: () => Rel, y: () => Rel) extends Cmd
  case class Reg(c: Constraint) extends Cmd
  case class DGet[T](v: DVar[Exp[T]], x: Exp[T]) extends Cmd
  case class DSet[T](v: DVar[Exp[T]], x: Exp[T]) extends Cmd
  case class Custom(s:String) extends Cmd {
    def run(rec: (() => Rel) => (() => Unit) => Unit)(k: () => Unit): Unit = {
      k()
    }
  }
  case object Yes extends Cmd
  case object No extends Cmd

  abstract class Rel
  case class TSX(x:Cmd) extends Rel

  var prog: Cmd = Yes

  var delayedMode = false

  implicit def reflectCmd(x:Cmd): Rel = {
    if (delayedMode) {
      val save = prog
      val pushFront = x match { case Reg(c) => true case _ => false }
      if (save == Yes) prog = x
      else if (pushFront) prog = And(() => x, () => {prog = save; TSX(Yes)})
      else prog = And(() => {prog = save; TSX(Yes)}, () => x)
      TSX(Yes)
    } else TSX(x)
  }

  def reifyCmd(x: => Rel): Cmd = {
    val save = prog
    try {
      if (delayedMode) {
        prog = Yes
        x
        prog
      } else {
        val TSX(r) = x
        r
      }
    } finally prog = save
  }



  def keys(c: Constraint): List[Int] = c match {
    case IsEqual(Exp(a),Exp(b)) => List(a,b)
    case IsTerm(a, _, _) => List(a)
  }
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
  val Backtrack = new Exception
  val cstore0: Set[Constraint] = Set.empty
  var cstore: Set[Constraint] = cstore0
  var cindex: Map[Int, Set[Constraint]] = Map.empty withDefaultValue Set.empty
  val dvars0: Map[Int, Any] = Map.empty //withDefault { case DVar(id,v) => v }
  var dvars: Map[Int, Any] = dvars0

  case class DVar[T](id: Int, default: T) extends (() => T) {
    dvar_set(id,default)
    def apply(): T = if (delayedMode) {
      val v = fresh[Any]
      reflectCmd(DGet(this.asInstanceOf[DVar[Exp[Any]]],v))
      v.asInstanceOf[T]
    } else dvar_get(id)
    def :=(v: T): Unit = if (delayedMode) {
      reflectCmd(DSet(this.asInstanceOf[DVar[Exp[Any]]],v.asInstanceOf[Exp[Any]]))
    } else dvar_set(id,v)
  }

  var dvarCount = 1 // FIXME: breaks if we start at 0 -- why?
  def DVar[T](v: T): DVar[T] = {
    val id = dvarCount
    dvarCount += 1
    new DVar[T](id, v)
  }

  def dvar_set[T](id: Int, v: T): Unit = dvars += id -> v
  def dvar_get[T](id: Int): T = dvars(id).asInstanceOf[T]
  def dvar_upd[T](id: Int)(f: T => T): Unit = dvars += id -> f(dvar_get(id))

  def register(c: Constraint): Unit = {
    if (cstore.contains(c)) return

    val fail = () => throw Backtrack

    val cnew = keys(c) flatMap { k => cindex(k) flatMap { c2 => prop(c,c2)(fail) }}

    cstore = cstore + c
    keys(c) foreach { k => cindex += k -> (cindex(k) + c) }

    cnew foreach register
  }

  def xinfix_===[T](a: => Exp[T], b: => Exp[T]): Rel = {
    val c = IsEqual(a,b)    
    //reflectCmd(Reg(c)) delayed mode may still want eager constraints
    register(c)
    TSX(Yes)
  }
  implicit class ExpOps[T](a: Exp[T]) {
    def ===[U](b: Exp[U]) = xinfix_===(a,b)
  }

  def xinfix_&&(a: => Rel, b: => Rel): Rel = {
    And(() => a,() => b)
  }
  def xinfix_||(a: => Rel, b: => Rel): Rel = {
    Or(() => a,() => b)
  }
  implicit class RelOps(a: => Rel) {
    def &&(b: => Rel) = xinfix_&&(a,b)
    def ||(b: => Rel) = xinfix_||(a,b)
  }

  def term[T](key: String, args: List[Exp[Any]]): Exp[T] = {
    val e = fresh[T]
    val c = IsTerm(e.id, key, args)
    //reflectCmd(Reg(c)) delayed mode may still want eager constraints
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
  def exists[T,U,V,W,X](f: (Exp[T],Exp[U],Exp[V],Exp[W],Exp[X]) => Rel): Rel = {
    f(fresh[T],fresh[U],fresh[V],fresh[W],fresh[X])
  }
  def exists[T,U,V,W,X,Y](f: (Exp[T],Exp[U],Exp[V],Exp[W],Exp[X],Exp[Y]) => Rel): Rel = {
    f(fresh[T],fresh[U],fresh[V],fresh[W],fresh[X],fresh[Y])
  }
  def exists[T,U,V,W,X,Y,Z](f: (Exp[T],Exp[U],Exp[V],Exp[W],Exp[X],Exp[Y],Exp[Z]) => Rel): Rel = {
    f(fresh[T],fresh[U],fresh[V],fresh[W],fresh[X],fresh[Y],fresh[Z])
  }
}

trait Engine extends Base {
  val DEPTH_MAX: Int = 2000
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
      val cstore1 = cstore
      val cindex1 = cindex
      val dvars1 = dvars
      try {
        d += 1
        val c = reifyCmd(e())
        c match {
          case g@Custom(s) =>
            g.run(rec)(f)
          case Reg(c) =>
            register(c)
            f()
          case DGet(v,x) =>
            register(IsEqual(dvar_get(v.id),x))
            f()
          case DSet(v,x) =>
            dvar_set(v.id,x)
            f()
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
        cstore = cstore1
        cindex = cindex1
        dvars = dvars1
        d = d1
      }
    }

    def propagate(): Boolean = { // propagate constraints and look for contradictions
      true
    }

    val varCount1 = varCount
    val Done = new Exception
    var rn = 0
    val res = new scala.collection.mutable.ListBuffer[String]()
    try {
      val q = fresh[T]
      rec(() => f(q)){() =>
        if (propagate()) {
          //println(extractStr(q))
          res += extractStr(q)
          rn += 1
          if (rn>=max) {
            throw Done
          }
        }
      }
    } catch {
      case Done => // OK
    } finally {
      //varCount = varCount1
    }

    res.toList
  }

  def dump(out: java.io.PrintWriter)(x: Exp[Any]): Unit = {
    val idx = cstore groupBy { case IsTerm(id, _ , _) => id case _ => -1 }
    val stack = new scala.collection.mutable.BitSet(varCount)
    val stack2 = new scala.collection.mutable.BitSet(varCount)
    val seenVars= new scala.collection.mutable.HashMap[Int,Int]
    def canon(x: Exp[Any]): String = {
      val id = (Set(x.id) ++ (cstore collect {
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

