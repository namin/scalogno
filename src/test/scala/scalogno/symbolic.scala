import scala.language.implicitConversions

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
  case class Union[T](guards: Map[Sym[Boolean], T]) extends Sym[T]
    { override def toString = guards.toString }


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

  implicit class TraversableOps[T[A] <: Traversable[A], A](x: Sym[T[A]]) {
    def foreach(f: (A) => Unit): Unit = x match {
      case Const(v) =>
        v.foreach(f)
      case Union(guards) =>
        guards.values map (_.foreach(f))
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




  // In some cases it might be fun to turn solve implicit
  def solve[T](x: Sym[T]): T = x match {
    case Const(value) => value
    case Union(guards) => guards.values.head // We just want one
    case Var(name) =>
      // TODO: shouldn't run every time
      Z3.run()
      Z3.model(name) match {
        case value : T =>
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
    var newlist = List[Sym[Int]]()

    for( x <- xs )
     // newlist = if (x >= 0) x :: newlist else newlist

     // "imperative" version
     //if (x >= 0)
       newlist = x :: newlist
       // What if we have multiple lines?

    newlist
  }


  test("concrete values") {

    // Calling with concrete values returns a concrete value
    expectResult(Const(9)) {
      myFunction(4,5)
    }

    expectResult(Const(-3)) {
      val result = reversePositive(List(3,-5,1,-3))

      // Solving a concrete value gives a concrete value
      solve(result).head
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

