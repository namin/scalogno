import scala.language.implicitConversions
import scala.language.higherKinds

import java.io._
import org.scalatest._


// This is growing too much. Maybe it's time to use ScalaZ3?
object Z3 {
  var out: PrintWriter = new PrintWriter(new FileOutputStream("out.smt"))
  var constraints: List[String] = Nil

  def zprintln(x:String) { constraints = constraints :+ x }

  var model: Map[String, Any] = Map.empty

  def run() {
    import scala.sys.process._

    constraints foreach(out.println(_))
    out.println("(check-sat)")
    out.println("(get-model)")

    out.close
    import scala.sys.process._
    val p = Process("z3 -smt2 out.smt")

    model = Z3Parser.parse(p.!!)
    out = new PrintWriter(new FileOutputStream("out.smt"))
  }

  import scala.util.parsing.combinator.syntactical.StandardTokenParsers
  import scala.util.parsing.input._
  object Z3Parser extends StandardTokenParsers {
    lexical.reserved ++= List("sat", "unsat", "model", "define", "fun", "Bool", "Int", "true", "false")
    lexical.delimiters ++= List("(", ")", "-")

    import lexical.NumericLit

    def model: Parser[Map[String, Any]] = (
        "sat" ~ "(" ~ "model" ~> rep(defineFun) <~ ")" ^^
          { case binds => binds.toMap }
      | failure("unable to parse output from Z3")
    )

    def defineFun: Parser[Pair[String, Any]] = (
      defineInt | defineBool
    )

    def defineInt: Parser[Pair[String, Any]] = (
        "(" ~ "define" ~ "-" ~ "fun" ~> ident ~ ("(" ~ ")" ~ "Int" ~> numericLit <~ ")") ^^
          { case name ~ value => name.toString -> value.toInt }
      | "(" ~ "define" ~ "-" ~ "fun" ~> ident ~ ("(" ~ ")" ~ "Int" ~ "(" ~ "-" ~> numericLit <~ ")" ~ ")") ^^
          { case name ~ value => name.toString -> -value.toInt }
    )

    def defineBool: Parser[Pair[String, Any]] = (
        "(" ~ "define" ~ "-" ~ "fun" ~> ident <~ "(" ~ ")" ~ "Bool" ~ "true" ~ ")" ^^
          { case name => name.toString -> true }
      | "(" ~ "define" ~ "-" ~ "fun" ~> ident <~ "(" ~ ")" ~ "Bool" ~ "false" ~ ")" ^^
          { case name => name.toString -> false }
    )


    def parse(stream: String): Map[String, Any] = {
      val tokens = new lexical.Scanner(stream)
      phrase(model)(tokens) match {
        case Success(map, _) =>
          map
        case e =>
          println(e)
          Map.empty
      }
    }
  }
}

trait SymProgram extends EmbeddedControls {
  import Z3.zprintln


  class Sym[T]
  // Isn't this some kind of monad? Reminds me of the Maybe monad. It is "maybe" concrete

  case class Const[T](x: T) extends Sym[T] { override def toString = x.toString }
  case class Var[T:Typ](name: String) extends Sym[T] { override def toString = name }
  case class Union[T](guards: Map[Sym[Boolean], T]) extends Sym[T] {
    override def toString = guards.toString

    def ++(other: Union[T]): Union[T] =
      Union[T]( guards ++ other.guards )
  }

  // TODO: The Vars can only be boolean or integers, and we don't keep
  // Unions of them. Shouldn't the types reflect this? What happens if
  // we have a Union of Ints or Bools? We should do something like
  // x2 = ite(b0, x0, x1) instead of Unions

  class Typ[T]

  implicit object boolTyp extends Typ[Boolean] { override def toString = "Bool" }
  implicit object intTyp  extends Typ[Int]     { override def toString = "Int"  }

  implicit def lift[T](x: T): Sym[T] = x match {
   case _ : Int     => Const[T](x)
   case _ : Boolean => Const[T](x)
   case _           => Const[T](x)
  }


  var nVars = 0
  def fresh[T:Typ]: Sym[T] = {
    zprintln(s"(declare-var x${nVars} ${implicitly[Typ[T]]})"); nVars += 1; Var[T](s"x${nVars - 1}")
  }

  def newvar[T:Typ](value: String): Sym[T] = {
//    zprintln(s"(define-const x${nVars} ${implicitly[Typ[T]]} ($value))"); nVars += 1;
    val v = fresh[T]
    zprintln(s"(assert (= $v ($value)))")
//    println(s"\t $v = ($value)")
    v
  }

  def infix_==[T:Typ](lhs: T, rhs: Sym[T]): Sym[Boolean] = newvar(s"= $rhs $lhs")
  def infix_==[T:Typ](lhs: Sym[T], rhs: T): Sym[Boolean] = newvar(s"= $rhs $lhs")
  def infix_==[T:Typ](lhs: Sym[T], rhs: Sym[T]): Sym[Boolean] = newvar(s"= $rhs $lhs")

  def assert(b: Sym[Boolean]): Unit = zprintln(s"(assert $b)")


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

  implicit class TraversableOps[T[A] <: Traversable[A], A](x: Sym[T[A]]) {
    def foreach(f: (A) => Unit): Unit = x match {
      case Const(v) =>
        v.foreach(f)
      case Union(guards) =>
        guards.values map (_.foreach(f))
    }
  }

  implicit class ListOps[A](x: Sym[List[A]]) {
    def ::(head: A): Sym[List[A]] = x match {
      case Const(tail) => Const(head :: tail)
      case Union(guards) =>
        Union( guards mapValues { tail => (head :: tail) } )
    }
  }

  implicit class IntOps(x: Sym[Int]) {
    def >(y: Sym[Int]) : Sym[Boolean] = (x,y) match {
      case (Const(a),Const(b)) => a > b
      case _                   => newvar(s"> $x $y")
    }
    def <(y: Sym[Int]) : Sym[Boolean] = (x,y) match {
      case (Const(a),Const(b)) => a < b
      case _                   => newvar(s"< $x $y")
    }
    def >=(y: Sym[Int]) : Sym[Boolean] = (x,y) match {
      case (Const(a),Const(b)) => a >= b
      case _                   => newvar(s">= $x $y")
    }
    def <=(y: Sym[Int]) : Sym[Boolean] = (x,y) match {
      case (Const(a),Const(b)) => a >= b
      case _                   => newvar(s"<= $x $y")
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


  def __ifThenElse[A, T <: Sym[A]](cond: Sym[Boolean], thenp: => T, elsep: => T): Sym[A] = cond match {
    case Const(true)  => thenp
    case Const(false) => elsep
    case Var(_) =>
      // TODO: this operation to extend unions should be implemented in the class Union
        (thenp match {
          case Const(v) => Union(Map( cond -> v ))
          case Union(guards) =>
            Union( guards map { case (k, v) => (cond && k) -> v } )
        }) ++
        (elsep match {
          case Const(v) => Union(Map( !cond -> v ))
          case Union(guards) =>
            Union( guards map { case (k, v) => (!cond && k) -> v } )
        })
  }

  // def __assign[Sym[T]](lhs: Sym[T], rhs: Sym[T]): Unit = {
  //   println(lhs)
  //   println(rhs)
  // }




  // In some cases it might be fun to turn solve implicit
  def solve[T](x: Sym[T]): T = x match {
    case Const(value) => value
    case Union(guards) =>
      guards collectFirst { case Pair(k,v) if solve(k) => v } match {
        case Some(value) => value
        case None => throw new Exception("No guard was true for Union value")
      }
    case Var(name) =>
      // TODO: shouldn't run every time
      Z3.run()
      Z3.model(name) match {
        case value : T =>
          // TODO: Gives warning due to type erasure
          // maybe we could change Z3.model into something like Map[Var[T], T]
          value
        case _ =>
          throw new Exception("Couldn't find value for" + name)
      }
  }

}


class TestSymbolic extends FunSuite with SymProgram {
  def myFunction(x: Sym[Int], y: Sym[Int]): Sym[Int] = {
    x + y;
  }

  def reversePositive(xs: Sym[List[Sym[Int]]]): Sym[List[Sym[Int]]] = {
    var newlist : Sym[List[Sym[Int]]] = List[Sym[Int]]()

    for( x <- xs )
//      newlist = x :: newlist
      newlist = if (x >= 0) x :: newlist else newlist
//      newlist = __ifThenElse[Sym[Int]](x >= 0, x :: newlist, newlist)

     // "imperative" version
     //if (x >= 0)
       // newlist = x :: newlist
       // What if we have multiple lines?

    newlist
  }


  def reverse(xs: Sym[List[Sym[Int]]]): Sym[List[Sym[Int]]] = {
    var newlist = List[Sym[Int]]()

    for( x <- xs )
       newlist = x :: newlist

    newlist
  }


  test("concrete values") {

    // Calling with concrete values returns a concrete value
    expectResult(Const(9)) {
      myFunction(4,5)
    }

    expectResult(Const(-3)) {
      val result = reverse(List(3,-5,1,-3))

      // Solving a concrete value gives a concrete value
      solve(result).head
    }

    expectResult(List(1,3)) {
      val result = reversePositive(List(3,-5,1,-3))
      solve(result) map solve
    }

  }

  test("symbolic values") {


    expectResult(Const(-3)) {
      val result = reverse(List(3,5,fresh[Int],fresh[Int],-3) : List[Sym[Int]])

      solve(result).head
    }

    expectResult(3) {
      val a = fresh[Int]
      val result = reversePositive(List(3,a,1,-3) : List[Sym[Int]])
      assert( a > 0 )
      (solve(result) map solve).length
    }

    expectResult(2) {
      val a = fresh[Int]
      val result = reversePositive(List(3,a,1,-3) : List[Sym[Int]])
      assert( a < 0 )
      (solve(result) map solve).length
    }

  }

  test("solve") {

    expectResult(42) {
      val a = fresh[Int]
      assert(a == 42)

      solve(a)
    }

    expectResult(-2) {
      val a = fresh[Int]
      val b = myFunction(3, a)

      val c = (1 == b)

      assert(c)
      solve(a)
    }

  }

}

