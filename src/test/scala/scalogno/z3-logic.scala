package scalogno

import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

import scala.language.implicitConversions

import java.io._


trait Z3LogicBase {

  class Typ[T]
  case class Exp[T](s: String) { override def toString = s }
  //case class Rel(s: String) { override def toString = s }
  type Fun2[A,B,C] = (Exp[A],Exp[B]) => Exp[C]
  type Fun[A,B] = Fun2[A,B,Boolean]

  type Rel = Exp[Boolean]
  def Rel(s: String) = Exp[Boolean](s)

  implicit object boolTyp extends Typ[Boolean]  { override def toString = "Bool" }
  implicit object intTyp extends Typ[Int]  { override def toString = "Int" }
  implicit object intListTyp extends Typ[List[Int]]  { override def toString = "(List Int)" }

  var depth = 0
  var maxDepth = 0

  var out: PrintWriter = null
  def zprintln(x:Any) = out.println("  "*(maxDepth-depth)+x)

  var nVars = 0

  def fresh[T:Typ]: Exp[T] = {
    zprintln(s"(declare-var x${nVars} ${implicitly[Typ[T]]})"); nVars += 1; Exp(s"x${nVars - 1}")
  }

  def rel(s: String): Rel = reflect[Boolean](s)

  def reflect[T:Typ](s: String): Exp[T] = {
    //val r = fresh[Boolean]
    //zprintln(s"(assert (= $r $s))")
    zprintln(s"(define-const x${nVars} ${implicitly[Typ[T]]} $s)"); 
    nVars += 1; Exp[T](s"x${nVars - 1}")
  }


  var seen = Set[String]()
  var allguards = Set[String]()

  var path = Rel("true")

  def fun[A:Typ,B:Typ,C:Typ](name: String)(f: Fun2[A,B,C]): Fun2[A,B,C] = { (x,y) =>
    if (!seen(name)) {
      zprintln(s"(declare-fun $name (${implicitly[Typ[A]]} ${implicitly[Typ[B]]}) ${implicitly[Typ[C]]})")
      seen += name
    }
    if (depth > 0) {
      depth -= 1
      zprintln(s";; IN  ($name $x $y)")
      val q = f(x,y)
      val r = reflect[C](s"($name $x $y)") // do we need the symbolic name??
      zprintln(s";; OUT ($name $x $y)")
      zprintln(s"(assert (= $r $q))")
      depth += 1
      r
    } else {
      allguards += s"$path"
      zprintln(s";; ABORT ($name $x $y) ") //guard $path")
      //rel(s"(=> $path ($name $x $y))")
      reflect[C](s"($name $x $y)")
    }
  }

  def lemma[A:Typ,B:Typ](name: String)(f: Fun2[A,B,Boolean]): Fun2[A,B,Boolean] = { (x,y) =>
    // TODO: predicate on  precondition

    val f1 = fun(name)(f) 
    val r = f1(x,y)
    zprintln(s"(assert $r)")
    r
  }

  def exists[T:Typ](f: Exp[T] => Rel): Rel = f(fresh)
  def cons[T](h: Exp[T], t: Exp[List[T]]): Exp[List[T]] = Exp(s"(insert $h $t)")
  def succ(t: Exp[Int]): Exp[Int] = Exp(s"(+ 1 $t)")
  def nil[T]: Exp[List[T]] = Exp(s"nil")
  def zero: Exp[Int] = Exp(s"0")
  
  implicit class TermOps[T](x: Exp[T]) {
    def !==(y: Exp[T]): Rel = Rel(s"(not (= $x $y))")
    def ===(y: Exp[T]): Rel = Rel(s"(= $x $y)")
  }

  def if_[T:Typ](c: Exp[Boolean])(a: => Exp[T])(b: => Exp[T]): Exp[T] = {
      val save = path
      //path = Exp(s"(and $save $c)")
      path = Exp(s"$c")
      val x1 = a
      //path = Exp(s"(and $save (not $c))")
      path = Exp(s"(not $c)")
      val y1 = b
      path = save
      //val r = fresh[T]
      reflect(s"(ite $c $x1 $y1)")
      //zprintln(s"(assert (=> $c (= ($r $x1))))")
      //zprintln(s"(assert (=> (not $c) (= ($r $y1))))")
      //r
  }

  implicit def boolExp(x: Boolean) = Exp[Boolean](x.toString)

  implicit class RelOps(x: Rel) {
    def &&(y: => Rel): Rel = if_(x) { y } { false }
    def ||(y: => Rel): Rel = if_(x) { true } { y }
    def unary_! = {
      val x1 = x
      Rel(s"(not $x1)")
    }
    def ===>(y: => Rel): Rel = (!x) || y
  }



/*
  implicit class RelOps(x: => Rel) {
    def &&(y: => Rel): Rel = {
      val save = path
      val x1 = x
      path = Rel(s"(and $path $x1)")
      val y1 = y
      path = save
      rel(s"(and $x1 $y1)")
    }
    def ||(y: => Rel): Rel = {
      val save = path
      val x1 = x
      path = save
      val y1 = y
      path = save
      Rel(s"(or $x1 $y1)")
    }
    def unary_! = {
      val x1 = x
      Rel(s"(not $x1)")
    }
    def ===>(y: => Rel): Rel = (!x) || y
  }
*/

  implicit def intExp(x: Int) = Exp[Int](x.toString)    

  implicit class IntOps(x: Exp[Int]) {
    def >(y: Exp[Int]) = Rel(s"(> $x $y)")
    def >=(y: Exp[Int]) = Rel(s"(>= $x $y)")
    def +(y: Exp[Int]) = Exp[Int](s"(+ $x $y)")
    def -(y: Exp[Int]) = Exp[Int](s"(- $x $y)")
  }
  

  def run[T:Typ](f: Exp[T] => Rel): String = {
    Stream.from(2).map(runD(_)(f)).dropWhile(_ == "maybe").head
  }

  def init() = { }

  def runD[T:Typ](maxDepth0: Int)(f: Exp[T] => Rel): String = {
    nVars = 0
    maxDepth = maxDepth0
    depth = maxDepth
    seen = Set[String]()
    allguards = Set[String]()
    path = Rel("true")
    out = new PrintWriter(new FileOutputStream("out.smt"))

    init()

    val x = fresh[T]
    val r = f(x)

    out.println("(echo \"" + s"query $x" + "\")")

    out.println(s"(push)")
    out.println("(echo \"test with guards -- functions unreachable\")")
    for (g <- allguards)
      out.println(s"(assert (not $g))")
    out.println(s"(assert $r)")
    out.println(s"(check-sat)")

    out.println("(echo \"" + s"look for $x" + "\")")

    out.println(s"(get-model)")
    out.println(s"(pop)")


    out.println(s"(push)")
    out.println("(echo \"test without guards\")")
    out.println(s"(assert $r)")
    out.println(s"(check-sat)")


    out.println(s"(get-model)")
    out.println(s"(pop)")

    out.println("(echo \"done\")")

    out.close

    import scala.sys.process._
    
    val s = Process("z3 -rs:42 -smt2 out.smt").lines_!.toArray
    // s.foreach(println)

    val Array(s1,s2) = s.filter(_.contains("sat"))

    val ss = s.dropWhile(!_.contains(s"define-fun $x ")).drop(1).takeWhile(!_.contains("define-fun"))
    val qr = "("+ss.map(_.trim).mkString(" ") // balance paren at the end

    //println("w   guards "+s1)
    //println("w/o guards "+s2)

    (s1,s2) match {
      case ("sat","sat") => qr
      case ("unsat","unsat") => "unsat"
      case ("unsat","sat") => "maybe"
    }
  }
}





class TestZ3L_Lists extends FunSuite with Z3LogicBase {

  // (list,size) relation
  type T = Int
  def size: Fun[List[T],Int] = fun("size") { (x,y) => 
    (x === nil && y === zero) ||
    exists[T] { h => exists[List[T]] { t => 
      x === cons(h,t) && y > 0 && size(t,y-1)
      // size(t,y-1) && x === cons(h,t) && y > 0  <--- paths are top down: writing it this way would unfold always
    }}
  }

  // a version without fresh variables
  def size2: Fun[List[T],Int] = fun("size") { (x,y) => 
    (x === nil && y === zero) || ((x !== nil) && {
      val t = Exp[List[T]](s"(tail $x)")
      y > 0 && size2(t,y-1)
    })
  }


  test("lists1") {

    // compute size given list and list given size

    expectResult("(2)") {
      run[Int] { x =>
        size(cons(1,cons(2,nil)), x)
      }
    }

    expectResult("((insert 4 (insert 3 nil)))") {
      run[List[Int]] { x =>
        size(x, 2)
      }
    }

    expectResult("(nil)") {
      run[List[Int]] { x =>
        size(cons(1,cons(2,x)), 2)
      }
    }

    expectResult("unsat") {
      run[List[Int]] { x =>
        size(cons(1,cons(2,cons(3,x))), 2)
      }
    }

    expectResult("unsat") {
      runD[List[Int]](3) { x1 =>
        !size(nil,0)
      }
    }

    expectResult("unsat") {
      runD[List[Int]](3) { x1 =>
        val s = fresh[Int]
        size(cons(0,nil),s) && (s !== 1)
      }
    }
  }

  test("lists2") {
    // simple proofs

    expectResult("unsat") {
      run[List[Int]] { x1 =>
        val stm = (size(x1,0) ===> (x1 === nil))
        !stm
      }
    }

    expectResult("unsat") {
      run[List[Int]] { x1 =>
        val s1 = fresh[Int]

        val stm = (size(x1,s1) && s1 === 0) ===> (x1 === nil)
        !stm
      }
    }

    expectResult("unsat") {
      run[List[Int]] { x1 =>
        val s1 = fresh[Int]

        val stm = (size(x1,s1) && s1 > 0) ===> (x1 !== nil)
        !stm
      }
    }


    /*
      CAVEAT:

      Negation behaves a bit unintuitively if we introduce
      fresh variables. Example:

        !size(cons(0,nil),1)

      We would like to get 'unsat' but get 'sat'.
      
      Why? Size introduces fresh variables, so we end up checking 

        t = fresh

        cons(0,nil) === cons(h,t) && 1 > 0 && size(t,0)

      Now of course an easy way to make this false is to
      pick t != nil. Then the rest doesn't even matter.

      The take-away is that our simple 'exists' is not existential
      quantification, but just introducing fresh vars.
      Should we use Z3's exist??
    */

    expectResult("(") {
      runD[List[Int]](3) { x1 =>
        !size(cons(0,nil),1)
      } // XXX: would like unsat, but get sat
    }


      // a deterministic version of 'size' without fresh vars behaves as expected

    expectResult("unsat") {
      runD[List[Int]](3) { x1 =>
        !size2(cons(0,nil),1)
      }
    }


    expectResult("unsat") {
      run[List[Int]] { x1 =>
        // !(P(n) => P(n+1)) == unsat    --->    P(n) => P(n+1)

        val z = fresh[Int]
        val s1 = fresh[Int]

        val stm = (size2(x1,s1)) ===> size2(cons(z,x1),s1+1)
        !stm
      }
    }

  }
}




class TestZ3L_Types extends FunSuite with Z3LogicBase {

  /* ------- some basic type system stuff ------- */

  trait Type
  implicit object typTyp extends Typ[Type]  { override def toString = "Type" }

  override def init() = {
    zprintln("(declare-datatypes () ((Type nat bot top (arrow (arg Type) (res Type)))))")
  }

  val nat = Exp[Type]("nat")
  val bot = Exp[Type]("bot")
  val top = Exp[Type]("top")
  def arrow(arg: Exp[Type], res: Exp[Type]) = Exp[Type](s"(arrow $arg $res)")
  def isArrow(t: Exp[Type]) = Rel(s"(is-arrow $t)")
  def arg(t: Exp[Type]) = Exp[Type](s"(arg $t)")
  def res(t: Exp[Type]) = Exp[Type](s"(res $t)")


  def subtp: Fun[Type,Type] = fun("subtp") { (t1: Exp[Type], t2: Exp[Type]) =>
    t2 === top ||
    t1 === bot ||
    t1 === nat && t2 === nat ||
    isArrow(t1) && isArrow(t2) && subtp(arg(t2),arg(t1)) && subtp(res(t1),res(t2))
  }

  test("types1") {

    expectResult("((arrow bot top))") {
      runD[Type](4) { t1 =>
        subtp(arrow(nat,nat),t1)
      }
    }

    expectResult("unsat") {
      runD[Type](3) { t1 =>
        val stm = subtp(t1,t1) ===> subtp(arrow(t1,t1),arrow(t1,t1))
        !stm
      }
    }
  }



  test("subtpRefl") {

    // prove subtp reflexivity by induction

    def subtpReflBody(t1:Exp[Type], XXX:Exp[Type]) = {
      !isArrow(t1) ||
      isArrow(t1) && subtpRefl(arg(t1),XXX) && subtpRefl(res(t1),XXX)
    } && subtp(t1,t1)

    def subtpRefl: Fun[Type,Type] = lemma("subtp-refl")(subtpReflBody)


    expectResult("unsat") {
      runD[Type](3) { t1 =>

        val stm = subtpReflBody(t1,fresh) // prove body of lemma
        !stm
      }
    }

  }

}
