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
  abstract class Rel
  case class Or(x: () => Rel, y: () => Rel) extends Rel
  case class And(x: () => Rel, y: () => Rel) extends Rel
  case object Yes extends Rel
  case object No extends Rel

  def keys(c: Constraint): List[Int] = c match {
    case IsEqual(Exp(a),Exp(b)) => List(a,b)
    case IsTerm(a, _, _) => List(a)
  }
  def prop(c1: Constraint, c2: Constraint)(fail: () => Nothing): List[Constraint] = (c1,c2) match {
    case (IsEqual(Exp(a),Exp(b)), IsTerm(a1, key, args)) if a == a1 =>
      List(IsTerm(b, key, args))
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

  def register(c: Constraint): Unit = {
    if (cstore.contains(c)) return

    val fail = () => throw Backtrack

    val cnew = keys(c) flatMap { k => cindex(k) flatMap { c2 => prop(c,c2)(fail) }}

    cstore = cstore + c
    keys(c) foreach { k => cindex += k -> (cindex(k) + c) }

    cnew foreach register
  }

  def infix_===[T](a: => Exp[T], b: => Exp[T]): Rel = {
    val c = IsEqual(a,b)
    register(c)
    Yes
  }
  implicit class ExpOps[T](a: Exp[T]) {
    def ===(b: Exp[T]) = infix_===(a,b)
  }

  def infix_&&(a: => Rel, b: => Rel): Rel = {
    And(() => a,() => b)
  }
  def infix_||(a: => Rel, b: => Rel): Rel = {
    Or(() => a,() => b)
  }
  implicit class RelOps(a: => Rel) {
    def &&(b: => Rel) = infix_&&(a,b)
    def ||(b: => Rel) = infix_||(a,b)
  }

  def term[T](key: String, args: List[Exp[Any]]): Exp[T] = {
    val e = fresh[T]
    val c = IsTerm(e.id, key, args)
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
}

trait Engine extends Base {
  val DEPTH_MAX: Int = 2000
  def run[T](on: Option[Int])(f: Exp[T] => Rel): Seq[String] = {
    var d: Int = 0
    def printd(x: Any) = println(" "*d+x)

    def rec(e: () => Rel)(f: () => Unit): Unit = {
      if (d == DEPTH_MAX) {
        printd("ABORD depth "+d)
        return
      }
      val d1 = d
      val cstore1 = cstore
      val cindex1 = cindex
      try {
        d += 1
        e() match {
          case Or(a,b) =>
            rec(a)(f)
            rec(b)(f)
          case And(a,b) =>
            rec(a) { () =>
              if (propagate())
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
        d = d1
      }
    }

    def propagate(): Boolean = { // propagate constraints and look for contradictions
      true
    }

    def dump(out: java.io.PrintWriter)(x: Exp[Any]): Unit = {
      val idx = cstore groupBy { case IsTerm(id, _ , _) => id case _ => -1 }
      val stack = new scala.collection.mutable.BitSet(varCount)
      val stack2 = new scala.collection.mutable.BitSet(varCount)
      var seenVars: Map[Int,Int] = Map.empty
      def canon(x: Exp[Any]): String = {
        val id = (Set(x.id) ++ (cstore collect {
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

    def dumpStr(x: Exp[Any]): String = {
      val out = new java.io.ByteArrayOutputStream
      dump(new java.io.PrintWriter(new java.io.OutputStreamWriter(out)))(x)
      out.toString
    }

    val varCount1 = varCount
    val Done = new Exception
    var rn: Int = 0
    val res = new scala.collection.mutable.ListBuffer[String]()
    try {
      val q = fresh[T]
      rec(() => f(q)){() =>
        if (propagate()) {
          res += dumpStr(q)
          rn += 1
          if (rn>=on.getOrElse(rn)) {
            throw Done
          }
        }
      }
    } catch {
      case Done => // OK
    } finally {
      varCount = varCount1
    }

    res.toList
  }
}

trait ListBase extends Base {
  def list(xs: String*): Exp[List[String]] = if (xs.isEmpty) nil else cons(term(xs.head,Nil),list(xs.tail:_*))

  def cons[T](hd: Exp[T], tl: Exp[List[T]]): Exp[List[T]] = term("cons",List(hd,tl))
  def nil: Exp[List[Nothing]] = term("nil",List())
  def pair[A,B](a: Exp[A], b: Exp[B]): Exp[(A,B)] = term("pair",List(a,b))

  object Cons {
    def unapply[T](x: Exp[List[T]]): Some[(Exp[T],Exp[List[T]])] = {
      val h = fresh[T]
      val t = fresh[List[T]]
      x === cons(h,t)
      Some((h,t))
    }
  }
  object Pair {
    def unapply[A,B](x: Exp[(A,B)]): Some[(Exp[A],Exp[B])] = {
      val a = fresh[A]
      val b = fresh[B]
      x === pair(a,b)
      Some((a,b))
    }
  }
}

trait Lf1 extends Base {
  trait LF
  def lf(s: Exp[LF], x: Exp[LF]): Exp[LF] = term("lf", List(s, x))
  def checktp(x: Exp[LF], y: Exp[LF]) = { x === lf(fresh,y); x }

  abstract class Term {
    type Self <: Term
    def apply(s: String,xs:List[Atom] = Nil): Self
    def =>:(a: Atom) = a.apply{ _ => this}.asInstanceOf[For[Self]]
  }
  case class Atom(lv: Exp[LF]) extends Term {
    type Self = Atom
    def apply(s: String,xs:List[Atom]) = Atom(lf(term(s,xs.map(_.lv)),lv))
    def apply[B<:Term](f: Atom => B) = For[B](this,f)
    def in[T](f: Atom => T): T = f(this)
    def typed(u: Atom) = { checktp(lv,u.lv); this }
    def ===(u: Atom) = lv === u.lv
  }
  case class For[B<:Term](u: Atom, f: Atom => B) extends Term {
    type Self = For[B#Self]
    def apply(s: String,xs:List[Atom]) = For(u, x => f(x)(s,xs:+x))
    def apply(x:Atom): B = f(x.typed(u))
  }
  object Term {
    def unapply(x: Exp[LF]) = Some(Atom(x))
  }
  def % = Atom(fresh)


  object typ extends Atom(term[LF]("type", Nil))

  object any {
    def apply[A<:Term](f: Atom => A) = new {
      def apply(): A = f(%)
      def apply(s: String): () => A#Self = () => apply()(s)
    }
    def apply[A<:Term](f: (Atom,Atom) => A) = new {
      def apply(): A = f(%,%)
      def apply(s: String): () => A#Self = () => apply()(s)
    }
    def apply[A<:Term](f: (Atom,Atom,Atom) => A) = new {
      def apply(): A = f(%,%,%)
      def apply(s: String): () => A#Self = () => apply()(s)
    }
    def apply[A<:Term](f: (Atom,Atom,Atom,Atom) => A) = new {
      def apply(): A = f(%,%,%,%)
      def apply(s: String): () => A#Self = () => apply()(s)
    }
  }
}

trait Naturals extends Lf1 {
  val nat = typ           ("nat")
  val z   = nat           ("z")
  val s   = (nat =>: nat) ("s")

  val add   = (nat =>: nat =>: nat =>: typ) ("add")
  val add_z = any { N =>
    add(z)(N)(N)
  } ("add_z")
  val add_s = any { (N1,N2,N3) =>
    add(N1)(N2)(N3) =>:
    add(s(N1))(N2)(s(N3))
  } ("add_s")

  def searchNat(n: Atom): Rel = {
    n === z ||
    %.in { m => n===s(m) && searchNat(m) }
  }
  def searchAdd(a: Atom): Rel = {
    a === add_z() ||
    %.in { a1 => a===add_s()(a1) && searchAdd(a1) }
  }
}
