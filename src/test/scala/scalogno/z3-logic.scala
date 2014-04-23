package scalogno

import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

import scala.language.implicitConversions

import java.io._


trait Z3LogicBase extends EmbeddedControls {

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

  def __ifThenElse[T](c: Boolean, a: => T, b: => T): T = c match { case true => a case false => b }
  def __ifThenElse[T:Typ](c: Exp[Boolean], a: => Exp[T], b: => Exp[T]): Exp[T] = {
      val save = path
      // XXX TBD: use full path or only last cond??
      /* 
        the way we emit path conditions has a large effect on 
        running time (full quine gen example):

          path = Exp(s"(and $save $c)")         -->   5s
          path = reflect(s"(and $save $c)")     -->  60s
          path = Exp(s"$c")                     --> 200s

        (i'm a bit surprised because i would have expected 
        (2) to be the fastest due to better sharing)
      */

      //path = reflect(s"(and $save $c)")
      path = Exp(s"(and $save $c)")
      //path = Exp(s"$c")
      val x1 = a
      //path = reflect(s"(and $save (not $c))")
      path = Exp(s"(and $save (not $c))")
      //path = Exp(s"(not $c)")
      val y1 = b
      path = save
      reflect(s"(ite $c $x1 $y1)")
      //val r = fresh[T]
      //zprintln(s"(assert (=> $c (= ($r $x1))))")
      //zprintln(s"(assert (=> (not $c) (= ($r $y1))))")
      //r
  }

  implicit def boolExp(x: Boolean) = Exp[Boolean](x.toString)

  implicit class RelOps(x: Rel) {
    def &&(y: => Rel): Rel = if (x) { y } else { false }
    def ||(y: => Rel): Rel = if(x) { true } else { y }
    def unary_! = {
      val x1 = x
      Rel(s"(not $x1)")
    }
    def ===>(y: => Rel): Rel = (!x) || y
  }


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
    
    val s = Process("time z3 -rs:0 -smt2 out.smt").lines_!.toArray  // XXX: strange, 0 is much better than 42? (for quine, 5s vs 75s)
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


class TestZ3L_Eval extends FunSuite with Z3LogicBase {

  /* ------- eval and quines ------- */

/*
  sealed abstract class Term
  case class Var(x: Int) extends Term
  case class Lambda(x: Int, y: Term) extends Term
  case class App(x: Term, y: Term) extends Term
  case object Quote extends Term

  sealed abstract class Value
  case class Closure(e:VEnv,x:Int,y:Term) extends Value
  case class Code(x:Term) extends Value

  sealed abstract class VOpt
  case class Some(x:Value) extends VOpt
  case object None extends VOpt

  sealed abstract class VEnv
  case object VNil extends VEnv
  case class VCons(x: Int, y: Value, tl: VEnv) extends VEnv

  TODO: get rid of boilerplate decls
*/
  trait Term
  trait Value
  trait VOpt
  trait VEnv
  implicit object termTyp extends Typ[Term] { override def toString = "Term" }
  implicit object valueTyp extends Typ[Value] { override def toString = "Value" }
  implicit object voptTyp extends Typ[VOpt] { override def toString = "VOpt" }
  implicit object venvTyp extends Typ[VEnv] { override def toString = "VEnv" }

  override def init() = {
    zprintln("""
(declare-datatypes () (
  (Term 
    (Var (vid Int))
    (Lit (lvl Int))
    (Lambda (param Int) (body Term))
    (App (func Term) (arg Term))
    Quote
  )
  (Value 
    (Closure (clenv VEnv) (clparam Int) (clbody Term))
    (Code (term Term))
    (Const (cvl Int))
  )
  (VOpt
    (VSome (get Value))
    VNone
  )
  (VEnv
    (VCons (name Int) (value Value) (tail VEnv))
    VNil
  )
))
""")
  }

  def Var(vid: Exp[Int]): Exp[Term] = Exp(s"(Var $vid)")
  def Lit(lvl: Exp[Int]): Exp[Term] = Exp(s"(Lit $lvl)")
  def Lambda(param: Exp[Int], body: Exp[Term]): Exp[Term] = Exp(s"(Lambda $param $body)")
  def App(fun: Exp[Term], arg: Exp[Term]): Exp[Term] = Exp(s"(App $fun $arg)")
  def Quote: Exp[Term] = Exp(s"Quote")

  implicit class TermOps(x: Exp[Term]) {
    def isVar:    Rel       = Rel(s"(is-Var $x)")
    def isLit:    Rel       = Rel(s"(is-Lit $x)")
    def isLambda: Rel       = Rel(s"(is-Lambda $x)")
    def isApp:    Rel       = Rel(s"(is-App $x)")
    def isQuote:  Rel       = Rel(s"(is-Quote $x)")
    def vid:      Exp[Int]  = Exp(s"(vid $x)")
    def lvl:      Exp[Int]  = Exp(s"(lvl $x)")
    def param:    Exp[Int]  = Exp(s"(param $x)")
    def body:     Exp[Term] = Exp(s"(body $x)")
    def func:      Exp[Term] = Exp(s"(func $x)")
    def arg:      Exp[Term] = Exp(s"(arg $x)")
  }

  def Closure(clenv: Exp[VEnv], clparam: Exp[Int], clbody: Exp[Term]): Exp[Value] = Exp(s"(Closure $clenv $clparam $clbody)")
  def Code(term: Exp[Term]): Exp[Value] = Exp(s"(Code $term)")
  def Const(cvl: Exp[Int]): Exp[Value] = Exp(s"(Const $cvl)")

  implicit class ValueOps(x: Exp[Value]) {
    def isClosure: Rel       = Rel(s"(is-Closure $x)")
    def isCode:    Rel       = Rel(s"(is-Code $x)")
    def clenv:     Exp[VEnv] = Exp(s"(clenv $x)")
    def clparam:   Exp[Int]  = Exp(s"(clparam $x)")
    def clbody:    Exp[Term] = Exp(s"(clbody $x)")
    def term:      Exp[Term] = Exp(s"(term $x)")
  }

  def VSome(get: Exp[Value]): Exp[VOpt] = Exp(s"(VSome $get)")
  def VNone: Exp[VOpt] = Exp(s"VNone")

  implicit class VOptOps(x: Exp[VOpt]) {
    def isVSome:    Rel       = Rel(s"(is-VSome $x)")
    def isVNone:    Rel       = Rel(s"(is-VNone $x)")
    def get:        Exp[Value]= Exp(s"(get $x)")

    def foreach(f: Exp[Value] => Exp[VOpt]): Exp[VOpt] = if (x.isVSome) f(x.get) else VNone
  }

  def VCons(name: Exp[Int], value: Exp[Value], tail: Exp[VEnv]): Exp[VEnv] = Exp(s"(VCons $name $value $tail)")
  def VNil: Exp[VEnv] = Exp(s"VNil")

  implicit class VEnvOps(x: Exp[VEnv]) {
    def isVCons:    Rel       = Rel(s"(is-VCons $x)")
    def isVNil:     Rel       = Rel(s"(is-VNil $x)")
    def name:       Exp[Int]  = Exp(s"(name $x)")
    def value:      Exp[Value]= Exp(s"(value $x)")
    def tail:       Exp[VEnv] = Exp(s"(tail $x)")
  }

  /* ---- evaluator with simple quotation ---- */

  /*
  def vlookup(e: VEnv, x: Int): VOpt = {
    e match {
      case VCons(x1,v1,tail) => if (x == x1) Some(v1) else vlookup(tail,x)
      case _ => None
    }
  }

  def eval(n: Int, e: VEnv, x: Term): VOpt = if (n <= 0) None else {
    x match {
      case Lambda(x,y) => Some(Closure(e,x,y))
      case App(Quote,y) => Some(Code(y))
      case Var(x) => vlookup(e,x)

      case App(x,y) => 
        eval(n-1,e,x) match {
          case Some(Closure(e1,x1,y1)) => 
            eval(n-1,e,y) match {
              case Some(v) => eval(n-1,VCons(x1,v,e1),y1)
              case None => None
            }
          case Some(Code(c1)) =>
            eval(n-1,e,y) match {
              case Some(Code(c2)) => Some(Code(App(c1,c2)))
              case _ => None
            }
          case _ => None
        }
      case _ => None
    }
  }*/
  
  def vlookup: Fun2[VEnv,Int,VOpt] = fun("lookup") { (e: Exp[VEnv], x: Exp[Int]) =>
    if (e.isVCons) {
      if (x === e.name) { VSome(e.value) } else { vlookup(e.tail,x) }
    } else {
      VNone
    }
  }

  def eval: Fun2[VEnv,Term,VOpt] = fun("eval") { (e: Exp[VEnv], x: Exp[Term]) =>
    if (x.isLambda)   VSome(Closure(e,x.param,x.body)) else
    if (x.isVar)      vlookup(e,x.vid) else
    if (x.isApp) {
      if (x.func.isQuote) VSome(Code(x.arg))
      else {
        /*val fun = eval(e,x.func)
        val arg = eval(e,x.arg)
        if (fun.isVSome && arg.isVSome && fun.get.isCode && arg.get.isCode) { 
          VSome(Code(App(fun.get.term, arg.get.term))) 
        } else if (fun.isVSome && arg.isVSome && fun.get.isClosure) { 
          eval(VCons(fun.get.clparam,arg.get,fun.get.clenv),fun.get.clbody)
        } else VNone*/
        for (fun <- eval(e,x.func); arg <- eval(e,x.arg)) {
          if (fun.isCode && arg.isCode)
            VSome(Code(App(fun.term, arg.term)))
          else if (fun.isClosure)
            eval(VCons(fun.clparam,arg,fun.clenv),fun.clbody)
          else VNone
        }
      }
    } else VNone
  }


  test("lookup") {
    expectResult("((VSome (Const 1)))") {
      runD[VOpt](5) { x1 =>

        val env = VCons(0,Const(0),VCons(1,Const(1),VCons(2,Const(2),VNil)))
        vlookup(env,1) === x1
      }
    }    
  }


  /* ---- a simple quine ---- 
  ((lambda (x)
    (list x (list (quote quote) x)))
   (quote
    (lambda (x)
     (list x (list (quote quote) x)))))
  */

  test("evalQuineForward") {
    // forward evaluation (depth=5 is enough)
    expectResult("((let ((a!1 (Lambda 0 (App (Var 0) (App (App Quote Quote) (Var 0)))))) (App a!1 (App Quote a!1))))") {
      runD[Term](5) { y =>
        val term = App(Lambda(0, App(Var(0), App(App(Quote,Quote), Var(0)))),
                   App(Quote,Lambda(0, App(Var(0), App(App(Quote,Quote), Var(0))))))
        eval(VNil,term) === VSome(Code(y))
      }
    }    
  }

  test("evalQuineVerify") {
    // verify quine
    expectResult("unsat") {
      runD[Value](5) { y =>
        val term = App(Lambda(0, App(Var(0), App(App(Quote,Quote), Var(0)))),
                   App(Quote,Lambda(0, App(Var(0), App(App(Quote,Quote), Var(0))))))
        eval(VNil,term) !== VSome(Code(term))
      }
    }    
  }

  /* now takes ~10s */
  test("evalQuineGenPartial") {
    // partially generate quine
    expectResult("((Lambda 0 (App (Var 0) (App (App Quote Quote) (Var 0)))))") {
      runD[Term](5) { y =>
        val term = App(y,
                   App(Quote,Lambda(0, App(Var(0), App(App(Quote,Quote), Var(0))))))
        eval(VNil,term) === VSome(Code(term))
      }
    }    
  }

  /* takes ~5s with rand seed 0, >100s with other seeds, 
  previously ~25s (commit ffb31e7ca007a0e4e3ead890d8749753fbdacb3e) */
  test("evalQuineGenFull") {
    // fully generate quine
/*
    previous result (commit ffb31e7ca007a0e4e3ead890d8749753fbdacb3e)
    expectResult("""((let ((a!1 (App (Lambda 4 (Lambda 4 (Var 4))) (App Quote (App Quote (Var 144))))) 
      (a!2 (App Quote (Lambda 4 (Lambda 4 (Var 4))))) 
      (a!3 (App Quote (App Quote (App Quote (Var 144))))) 
      (a!4 (App (App (Lambda 72 (App Quote Quote)) (Lambda 73 (Var 110))) (Var 54)))) 
      (let ((a!5 (Lambda 54 (App (App (App a!2 a!3) (Var 54)) a!4)))) 
        (let ((a!6 (App a!1 (App (Lambda 42 a!5) (Lambda 45 (Var 257))))) 
          (a!7 (App Quote (App (Lambda 42 a!5) (Lambda 45 (Var 257)))))) 
            (App a!6 a!7)))))""".replaceAll("\n"," ").replaceAll(" +"," ")) {

    now we're actually getting the simple one we'd expect
*/

    expectResult("((let ((a!1 (Lambda 81 (App (Var 81) (App (App Quote Quote) (Var 81)))))) (App a!1 (App Quote a!1))))") {
      runD[Term](5) { y =>
        val term = y
        eval(VNil,term) === VSome(Code(term))
      }
    }    
  }


}