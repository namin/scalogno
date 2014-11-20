import scala.language.implicitConversions

import java.io._

object Z3 {
  var out: PrintWriter = new PrintWriter(new FileOutputStream("out.smt"))
  def zprintln(x:Any) = out.println(x)

  def run() {
    import scala.sys.process._

    zprintln("(check-sat)")
    zprintln("(get-model)")

    out.close
    import scala.sys.process._
    val s = Process("z3 -smt2 out.smt").lines_!

    s foreach println
  }
}

trait SymProgram extends EmbeddedControls {
  import Z3.zprintln


  class Sym[T]
  // Isn't this some kind of monad? Reminds me of the Maybe monad. It is "maybe" concrete
  case class Const[T](x: T) extends Sym[T] { override def toString = x.toString }
  // TODO: a const is actually a Union with one guard (true). How can we reflect this?
  case class Var[T](name: String) extends Sym[T] { override def toString = name }
  case class Union[T](guards: Map[Sym[Boolean], T], varGuards: Map[Sym[Boolean], Var[T]]) extends Sym[T]
    { override def toString = guards.toString }
  // TODO: implement union as a list of "guards", which should be a new type
  // that can either be of the form (cond -> value) or (cond -> variable)


  class Typ[T]

  implicit object boolTyp extends Typ[Boolean] { override def toString = "Bool" }
  implicit object intTyp  extends Typ[Int]     { override def toString = "Int"  }

  implicit def lift[T](x: T): Sym[T] = x match {
   case _ : Int     => Const[T](x)
   case _ : Boolean => Const[T](x)
   case _           => Union[T]( Map(lift(true) -> x), Map.empty )
  }


  var nVars = 0
  def fresh[T:Typ]: Sym[T] = {
    zprintln(s"(declare-var x${nVars} ${implicitly[Typ[T]]})"); nVars += 1; Var[T](s"x${nVars - 1}")
  }

  def newvar[T:Typ](value: String): Sym[T] = {
//    zprintln(s"(define-const x${nVars} ${implicitly[Typ[T]]} ($value))"); nVars += 1;
    val v = fresh[T]
    zprintln(s"(assert (= $v ($value)))")
    println(s"\t $v = ($value)")
    v
  }

  def infix_==[T:Typ](lhs: T, rhs: Sym[T]): Sym[Boolean] = newvar(s"= $rhs $lhs")
  def infix_==[T:Typ](lhs: Sym[T], rhs: T): Sym[Boolean] = newvar(s"= $rhs $lhs")
  def infix_==[T:Typ](lhs: Sym[T], rhs: Sym[T]): Sym[Boolean] = newvar(s"= $rhs $lhs")

  def assert(b: Sym[Boolean]): Unit = zprintln(s"(assert $b)")

  def infix_+(lhs: Sym[Int], rhs: Sym[Int]): Sym[Int] =
    (lhs, rhs) match {
      case (Const(x), Const(y)) =>
        Const(x + y)
      case _ =>
        newvar(s"+ $rhs $lhs")
    }


  // implicit def liftElements[A, T[A] <: Traversable[A]](x: T[A]): T[Sym[A]] = {
  //   val temp = ((x : T[A]) map : )lift
  //   temp
  // }

  implicit def liftElements[T](x: List[T]): List[Sym[T]] = {
    x map lift
  }

  implicit def liftList[T](x: List[T]): Sym[List[Sym[T]]] = {
    lift(x map lift)
  }

  // Not sure of what is the right way to to this
  implicit def traversableToOps[A, T[A] <: Traversable[A]](x: Sym[T[A]]) =
    TraversableOps[T[A], A](x)
  implicit class TraversableOps[T <: Traversable[A], A](x: Sym[T]) {
    def foreach(f: (A) => Unit): Unit = x match {
      case Union(guards, varGuards) =>
        // TODO: other cases
        guards(true).foreach(f)
    }
  }


  implicit class IntOps(x: Sym[Int]) {
    def >(y: Sym[Int]) : Sym[Boolean] = (x,y) match {
      case (Const(a),Const(b)) => a > b
      case _                   => newvar(s"> $x $y")
    }
    def >=(y: Sym[Int]) : Sym[Boolean] = (x,y) match {
      case (Const(a),Const(b)) => a > b
      case _                   => newvar(s">= $x $y")
    }
    def +(y: Sym[Int]) : Sym[Int] = (x,y) match {
      case (Const(a),Const(b)) => a + b
      case _                   => newvar(s"+ $x $y")
    }
    def -(y: Sym[Int]) : Sym[Int] = (x,y) match {
      case (Const(a),Const(b)) => a - b
      case _                   => newvar(s"- $x $y")
    }
  }

  implicit class BoolOps(x: Sym[Boolean]) {
    def unary_!(): Sym[Boolean] = x match {
      case Const(a) => !a
      case _        => newvar(s"not $x")
    }
    def &&(y: Sym[Boolean]) : Sym[Boolean] = (x,y) match {
      case (Const(a),Const(b)) => a && b
      case _                   => newvar(s"and $x $y")
    }
  }


  // def __ifThenElse[T](cond: Sym[Boolean], thenp: => T, elsep: => T): Sym[T] = cond match {
  //   case Const(true)  => Const(thenp)
  //   case Const(false) => Const(elsep)
  //   case Var(_)       => Union( Map(cond -> thenp, !cond -> elsep) )
  // }

  // def __ifThenElse[T](cond: Sym[Boolean], thenp: => Sym[T], elsep: => Sym[T]): Sym[T] = cond match {
  //   case Const(true)  => thenp
  //   case Const(false) => elsep
  //   case Var(_) =>
      // TODO: operation to extend unions
  //     Union(
  //       (thenp match {
  //         case Const(_) | Var(_) => Map( cond -> thenp )
  //         case Union(guards) =>
  //           guards map { case (k,v) => (cond && k) -> v }
  //       }) ++
  //       (elsep match {
  //         case Const(_) | Var(_) => Map( !cond -> thenp )
  //         case Union(guards) =>
  //           guards map { case (k,v) => (!cond && k) -> v }
  //       }))
  // }

  // def __assign[Sym[T]](lhs: Sym[T], rhs: Sym[T]): Unit = {
  //   println(lhs)
  //   println(rhs)
  // }

}



object Test extends SymProgram {
  def myFunction(x: Sym[Int], y: Sym[Int]): Sym[Int] = {
    x + y;
  }

   def reversePositive(xs: Sym[List[Sym[Int]]]): Sym[List[Sym[Int]]] = {
     var newlist = List[Sym[Int]]()

     for( x <- xs )
      // newlist = if (x >= 0) x :: newlist else newlist

      // "imperative" version
      //if (x >= 0)
        newlist = x :: newlist
        // What if we have multiple lines?

     newlist
   }


  def main(args : Array[String]) {
    val a = fresh[Int]
    val b = myFunction(3, a)
    println(myFunction(4,5))

    val c = (1 == b)

    assert(c)
    println(b)

    val list = List(3,-5,1,-3)
    println(list)
    println(reversePositive(list))

    val symbolicList : List[Sym[Int]] = List(3,a,1,-3)
    println(symbolicList)
    println(reversePositive(symbolicList))

    Z3.run()
  }
}

