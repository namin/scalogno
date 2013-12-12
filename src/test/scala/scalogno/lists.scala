package scalogno

import scala.language.implicitConversions

trait InjectBase extends Base {

  trait Inject[T] {
    def toTerm(x:T): Exp[T]
  }

  implicit def inject[T:Inject](x:T) = implicitly[Inject[T]].toTerm(x)

  implicit object InjectString extends Inject[String] {
    def toTerm(s: String): Exp[String] = term(s,Nil)
  }

}


trait Ordering extends Base {

  trait Ord[T] {
    def lt(x:Exp[T],y:Exp[T]): Rel
  }

  implicit class OrdOps[T:Ord](x:Exp[T]) {
    def <(y:Exp[T]): Rel = implicitly[Ord[T]].lt(x,y)
  }

}



trait NatBase extends InjectBase with Ordering {
  implicit val injectNat = new Inject[Int] {
    def toTerm(x: Int): Exp[Int] = nat(x)
  }
  implicit val ordNat = new Ord[Int] {
    def lt(x:Exp[Int],y:Exp[Int]): Rel = lessThan(x,y)
  }

  def nat(x: Int): Exp[Int] = if (x == 0) zero else succ(x-1)

  def succ(n: Exp[Int]): Exp[Int] = term("s",List(n))
  def zero: Exp[Int] = term("z",List())

  def lessThan(a: Exp[Int], b: Exp[Int]): Rel = 
    exists[Int] { b1 => b === succ(b1) && { a === zero || exists[Int] { a1 =>
      (a === succ(a1)) && lessThan(a1,b1)
    }}}

}




trait ListBase extends InjectBase with NatBase with Ordering {
  implicit def injectList[T:Inject] = new Inject[List[T]] {
    def toTerm(x: List[T]): Exp[List[T]] = list(x:_*)
  }
  implicit def ordList[T:Ord] = new Ord[List[T]] {
    def lt(x:Exp[List[T]],y:Exp[List[T]]): Rel = lessLex[T]((a1,a2) => a1 < a2, x,y)
  }

  def list[T:Inject](xs: T*): Exp[List[T]] = if (xs.isEmpty) nil else cons(inject(xs.head),list(xs.tail:_*))

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


  def append[T](as: Exp[List[T]], bs: Exp[List[T]], cs: Exp[List[T]]): Rel =
    (as === nil && bs === cs) ||
    exists[T,List[T],List[T]] { (h,t1,t2) =>
      (as === cons(h,t1)) && (cs === cons(h,t2)) && append(t1,bs,t2)
    }

  def map[T,U](f: (Exp[T],Exp[U]) => Rel, as: Exp[List[T]], bs: Exp[List[U]]): Rel =
    (as === nil) && (bs === nil) ||
    exists[T,U,List[T],List[U]] { (a,b,as1,bs1) =>
      (as === cons(a,as1)) && f(a,b) && (bs === cons(b,bs1)) && map[T,U](f,as1,bs1)
    }

  def flatMap[T,U](f: (Exp[T],Exp[List[U]]) => Rel, as: Exp[List[T]], cs: Exp[List[U]]): Rel =
    (as === nil) && (cs === nil) ||
    exists[T,List[U],List[T],List[U]] { (a,bs,as1,cs1) =>
      (as === cons(a,as1)) && f(a,bs) && append(bs, cs1, cs) && flatMap[T,U](f,as1,cs1)
    }


  def lessLex[T](f: (Exp[T],Exp[T]) => Rel, as: Exp[List[T]], bs: Exp[List[T]]): Rel =
    exists[T,List[T]] { (b,bs1) => (bs === cons(b,bs1)) && { (as === nil) ||
      exists[T,List[T]] { (a,as1) =>
        (as === cons(a,as1)) && { f(a,b) || (a === b) && lessLex[T](f,as1,bs1) }
      }
    }}
}

trait TreeBase extends InjectBase with NatBase with Ordering {

  trait Tree[+T,-U]

  implicit def injectPair[T:Inject,U:Inject](x: (T,U)) = (inject(x._1), inject(x._2))

  def tree[T,U](xs: (Exp[T],Exp[U])*): Exp[Tree[T,U]] = if (xs.length == 0) empty else {
    val n = xs.length/2
    val (k,v) = xs(n)
    branch(tree(xs.slice(0,n):_*),k,v,tree(xs.slice(n+1,xs.length):_*))
  }

  def branch[T,U](l: Exp[Tree[T,U]], k: Exp[T], v: Exp[U], r: Exp[Tree[T,U]]): Exp[Tree[T,U]] = term("branch",List(l,k,v,r))
  def leaf[T,U](k:Exp[T],v: Exp[U]) = branch(empty,k,v,empty)
  def empty: Exp[Tree[Nothing,Any]] = term("nil",List())

  def lookupAll[T,U](as: Exp[Tree[T,U]], k: Exp[T], v: Exp[U]): Rel =
    exists[Tree[T,U],Tree[T,U],T,U] { (l,r,k1,v1) => 
      as === branch(l,k1,v1,r) && {
        (k === k1 && v === v1) ||
        lookupAll(l,k,v) || lookupAll(r,k,v)
      }
    }

  def lookup[T:Ord,U](as: Exp[Tree[T,U]], k: Exp[T], v: Exp[U]): Rel =
    exists[Tree[T,U],Tree[T,U],T,U] { (l,r,k1,v1) => 
      as === branch(l,k1,v1,r) && {
        (k === k1 && v === v1) ||
        (k < k1 && lookup(l,k,v)) || 
        (k1 < k && lookup(r,k,v))
      }
    }

  def lookupLess[T:Ord,U](as: Exp[Tree[T,U]], k: Exp[T], v: Exp[U]): Rel =
    exists[Tree[T,U],Tree[T,U],T,U] { (l,r,k1,v1) => 
      as === branch(l,k1,v1,r) && {
        (lookupLess(l,k,v)) || 
        (k1 < k && v === v1) ||
        (k1 < k && lookupLess(r,k,v))
      }
    }

}

trait GraphBase extends InjectBase with NatBase {

  trait Graph[T] {
    def edge(a: Exp[T], b: Exp[T]): Rel
    def path(a: Exp[T], b: Exp[T]): Rel =
      edge(a,b) || exists[T] { z => edge(a,z) && path(z,b) }
  }

}

trait MetaGraphBase extends GraphBase with ListBase {

/*
(define (patho-clause head tail) 
  (fresh (x y)
    (== head ‘(patho ,x ,y)) 
    (conde
      ((edgeo x y) (== tail ’())) 
      ((fresh (z)
        (edgeo x z)
        (== tail ‘((patho ,z ,y))))))))
*/

  def pathTerm[T](a: Exp[T], b: Exp[T]) = term("path",List(a,b))

  def pathClause1[T](g: Graph[T])(head: Exp[Any], body: Exp[List[Any]]) = {
    exists[T,T] { (a,b) => 
      (head === pathTerm(a,b)) && {
        g.edge(a,b) && (body === nil) ||
        exists[T] { z =>
          g.edge(a,z) && (body === pathTerm(z,b))
        }
      }
    }
  }

  type Clause = (Exp[Any], Exp[List[Any]]) => Rel

  def existsC[T,U](f: (Exp[T],Exp[U]) => Clause): Clause = {
    f(fresh[T],fresh[U])
  }

  def pathClause2[T](g: Graph[T])(a: Exp[T], b: Exp[T]) = { (head: Exp[Any], body: Exp[List[Any]]) =>
    (head === pathTerm(a,b)) && {
      g.edge(a,b) && (body === nil) ||
      exists[T] { z =>
        g.edge(a,z) && (body === pathTerm(z,b))
      }
    }
  }


}

trait ReifyUtilsBase extends Base with InjectBase with ListBase with Engine {
  def rule[T,U](s: String)(f: (Exp[T],Exp[U]) => Rel): (Exp[T],Exp[U]) => Rel
  def globalTrace: () => Exp[List[List[String]]]
}

trait ReifyUtilsDynVars extends ReifyUtilsBase with InjectBase with ListBase with Engine {
  val globalTrace = DVar(nil: Exp[List[List[String]]])

  def rule[T,U](s: String)(f: (Exp[T],Exp[U]) => Rel): (Exp[T],Exp[U]) => Rel = 
    { (a,b) =>
      globalTrace := cons(term(s,List(a,b)), globalTrace())
      f(a,b)
    }
}

trait ReifyUtils extends ReifyUtilsBase with InjectBase with ListBase with Engine {

  var globalTrace0: Exp[List[List[String]]] = nil

  def globalTrace = () => globalTrace0
  def globalTrace_=(x:Exp[List[List[String]]]) = globalTrace0 = x

  // inject non-std interpretation by overriding || and &&

  override def infix_||(a: => Rel, b: => Rel): Rel = {
    val localTrace = globalTrace()
    def reset(x: => Rel) = { globalTrace = localTrace; x }
    super.infix_||(reset(a),reset(b))
  }
  override def infix_&&(a: => Rel, b: => Rel): Rel = {
    val localTrace = globalTrace()
    def reset(x: => Rel) = { globalTrace = localTrace; x }
    super.infix_&&(reset(a),b) // do not reset b
  }

  def rule[T,U](s: String)(f: (Exp[T],Exp[U]) => Rel): (Exp[T],Exp[U]) => Rel = 
    { (a,b) => 
      globalTrace = cons(term(s,List(a,b)),globalTrace()); 
      f(a,b)
    }

  // inject non-std interpretation by transforming rules reified as Or and And

  var inrule: List[String] = Nil
  def rule0[T,U](s: String)(f: (Exp[T],Exp[U]) => Rel): (Exp[T],Exp[U]) => Rel = 
    { (a,b) => 
      val self = s + "(" + extractStr(a) + "," + extractStr(b) + ")"
      val local = self::inrule
      //println("enter " + self + " at " + inrule.mkString(",")); 

      val localTrace = cons(term(s,List(a,b)),globalTrace())

      def vprintln(s: Any) = () // println(s)

      try {         
        def rec(n:Int)(r: Rel): Rel = r match {
          case Or(a,b) => 
            Or(() => { inrule = local; globalTrace = localTrace; vprintln("left  in "+n+self); rec(n+1)(a()) }, 
               () => { inrule = local; globalTrace = localTrace; vprintln("right in "+n+self); rec(n+1)(b()) })
          case And(a,b) => 
            And(() => { inrule = local; globalTrace = localTrace; vprintln("fst in "+n+self); rec(n+1)(a()) }, 
                () => { inrule = local; globalTrace = localTrace; vprintln("snd in "+n+self); rec(n+1)(b()) }) // should not reset?
          case _ => r
        }
        rec(0)(f(a,b))
      } finally {
        inrule = local.tail
      }
    }

}





import org.scalatest._

class TestNats extends FunSuite with Base with Engine with NatBase with ListBase {

  test("lte") {
    expectResult(List("s(s(s(s(x0))))")) {
      run[Int] { q =>
        lessThan(3, q)
      }
    }
  }

}

class TestLists extends FunSuite with Base with Engine with NatBase with ListBase {

  test("append") {
    expectResult(List("cons(a,cons(b,cons(c,cons(d,cons(e,cons(f,nil))))))")) {
      run[List[String]] { q =>
        append(list("a","b","c"), list("d","e","f"), q)
      }
    }
    expectResult(List("cons(d,cons(e,cons(f,nil)))")) {
      run[List[String]] { q =>
        append(list("a","b","c"), q, list("a","b","c","d","e","f"))
      }
    }
    expectResult(List("cons(a,cons(b,cons(c,nil)))")) {
      run[List[String]] { q =>
        append(q, list("d","e","f"), list("a","b","c","d","e","f"))
      }
    }
    expectResult(List(
      "pair(nil,cons(a,cons(b,cons(c,cons(d,cons(e,cons(f,nil)))))))", 
      "pair(cons(a,nil),cons(b,cons(c,cons(d,cons(e,cons(f,nil))))))", 
      "pair(cons(a,cons(b,nil)),cons(c,cons(d,cons(e,cons(f,nil)))))", 
      "pair(cons(a,cons(b,cons(c,nil))),cons(d,cons(e,cons(f,nil))))", 
      "pair(cons(a,cons(b,cons(c,cons(d,nil)))),cons(e,cons(f,nil)))", 
      "pair(cons(a,cons(b,cons(c,cons(d,cons(e,nil))))),cons(f,nil))", 
      "pair(cons(a,cons(b,cons(c,cons(d,cons(e,cons(f,nil)))))),nil)"
    )) {
      run[(List[String],List[String])] { q =>
        val q1,q2 = fresh[List[String]]
        (q === pair(q1,q2)) &&
        append(q1, q2, list("a","b","c","d","e","f"))
      }
    }
  }

  test("pair") {
    expectResult(List(
      "pair(nil,cons(a,cons(b,cons(c,cons(d,cons(e,cons(f,nil)))))))", 
      "pair(cons(a,nil),cons(b,cons(c,cons(d,cons(e,cons(f,nil))))))", 
      "pair(cons(a,cons(b,nil)),cons(c,cons(d,cons(e,cons(f,nil)))))", 
      "pair(cons(a,cons(b,cons(c,nil))),cons(d,cons(e,cons(f,nil))))", 
      "pair(cons(a,cons(b,cons(c,cons(d,nil)))),cons(e,cons(f,nil)))", 
      "pair(cons(a,cons(b,cons(c,cons(d,cons(e,nil))))),cons(f,nil))", 
      "pair(cons(a,cons(b,cons(c,cons(d,cons(e,cons(f,nil)))))),nil)"
    )) {
      run[(List[String],List[String])] {
        case Pair(q1,q2) =>
          append(q1, q2, list("a","b","c","d","e","f"))
      }
    }
    expectResult(List("pair(x0,x0)")) {
      run[(List[String],List[String])] {
        case Pair(q1,q2) => q1 === q2
      }
    }
  }


  test("map") {
    expectResult(List("cons(a,cons(b,cons(c,cons(d,cons(e,cons(f,nil))))))")) {
      run[List[String]] { q =>
        map[String,String]((q1,q2) => q1 === q2 , list("a","b","c","d","e","f"), q)

      }
    }
    def elems = (List("a","b","c","d","e","f") map (term(_,Nil)),List("A","B","C","A","B","C") map (term(_,Nil))).zipped map (pair(_,_))
    def f(xs:List[Exp[(String,String)]])(e1:Exp[String],e2:Exp[String]): Rel = xs match {
      case Nil => No
      case x::xs => 
        //println(extractStr(x))
        (pair(e1,e2) === x) || f(xs)(e1,e2)
    }
    expectResult(List("cons(A,cons(B,cons(C,cons(A,cons(B,cons(C,nil))))))")) {
      run[List[String]] { q =>
        map[String,String](f(elems), list("a","b","c","d","e","f"), q)
      }
    }
    expectResult(List(
      "cons(a,cons(b,cons(a,nil)))", 
      "cons(a,cons(b,cons(d,nil)))", 
      "cons(a,cons(e,cons(a,nil)))", 
      "cons(a,cons(e,cons(d,nil)))", 
      "cons(d,cons(b,cons(a,nil)))", 
      "cons(d,cons(b,cons(d,nil)))", 
      "cons(d,cons(e,cons(a,nil)))", 
      "cons(d,cons(e,cons(d,nil)))"
    )){
      run[List[String]] { q =>
        map[String,String](f(elems), q, list("A","B","A"))
      }
    }
  }


  test("flatMap") {
    expectResult(List("cons(a,cons(a,cons(b,cons(b,cons(c,cons(c,nil))))))")) {
      run[List[String]] { q =>
        flatMap[String,String]((q1,q2) => q2 === cons(q1,cons(q1,nil)), list("a","b","c"), q)
      }
    }
    expectResult(List("cons(a,cons(b,cons(c,nil)))")) {
      run[List[String]] { q =>
        flatMap[String,String]((q1,q2) => q2 === cons(q1,cons(q1,nil)), q, list("a","a","b","b","c","c"))
      }
    }
  }

  test("lessThan") {
    expectResult(List(
      "nil", 
      "cons(z,nil)", 
      "cons(z,cons(z,x0))", 
      "cons(z,cons(s(z),nil))", 
      "cons(z,cons(s(z),cons(z,x0)))", 
      "cons(z,cons(s(z),cons(s(z),x0)))"
    )) {
      run[List[Int]] { q =>
        lessLex[Int]((q1,q2) => lessThan(q1,q2), q, list(0,1,2))
      }
    }
  }
  test("lessThanOrd") {
    expectResult(List(
      "nil", 
      "cons(z,nil)", 
      "cons(z,cons(z,x0))", 
      "cons(z,cons(s(z),nil))", 
      "cons(z,cons(s(z),cons(z,x0)))", 
      "cons(z,cons(s(z),cons(s(z),x0)))"
    )) {
      run[List[Int]] { q =>
        q < List(0,1,2)
      }
    }
  }
}


class TestTrees extends FunSuite with Base with Engine with NatBase with ListBase with TreeBase {

  test("tree") {
    expectResult(List(
      "branch(branch(branch(nil,s(z),a,nil),s(s(z)),b,nil),s(s(s(z))),c,branch(nil,s(s(s(s(z)))),d,nil))"
    )) {
      run[List[String]] { q =>
        q === tree(1 -> "a", 2 -> "b", 3 -> "c", 4 -> "d")
      }
    }
  }

  test("lookupAll") {
    expectResult(List("c")) {
      run[String] { q =>
        val t = tree(1 -> "a", 2 -> "b", 3 -> "c", 4 -> "d")
        lookupAll(t,3,q)
      }
    }
  }

  test("lookupOrd") {
    expectResult(List("c")) {
      run[String] { q =>
        val t = tree(1 -> "a", 2 -> "b", 3 -> "c", 4 -> "d")
        lookup(t,3,q)
      }
    }
    expectResult(List("b")) {
      run[String] { q =>
        val t = tree(List(1,1,1) -> "a", List(1,2,2) -> "b", List(2,1,1) -> "c", List(3,2,2) -> "d")
        lookup(t,List(1,2,2),q)
      }
    }
    expectResult(List("c")) {
      run[String] { q =>
        val t = tree(List(1,1,1) -> "a", List(1,2,2) -> "b", List(2,1,1) -> "c", List(3,2,2) -> "d")
        lookup(t,List(2,1,1),q)
      }
    }
    expectResult(Nil) {
      run[String] { q =>
        val t = tree(List(1,1,1) -> "a", List(1,2,2) -> "b", List(2,1,1) -> "c", List(3,2,2) -> "d")
        lookup(t,List(2,2,2),q)
      }
    }
    expectResult(List("a","b","c")) {
      run[String] { q =>
        val t = tree(List(1,1,1) -> "a", List(1,2,2) -> "b", List(2,1,1) -> "c", List(3,2,2) -> "d")
        lookupLess(t,List(2,2,2),q)
      }
    }
  }

  test("lookup with holes") {
    expectResult(List("s(s(z))")) {
      run[Int] { q =>
        val t = tree(List(1,1,1) -> "a", List(1,2,2) -> "b", cons(q,List(1,1)) -> inject("c"), List(3,2,2) -> "d")
        lookup(t,List(2,1,1),"c")
      }
    }
    expectResult(List("s(z)")) {
      run[Int] { q =>
        val t = tree(List(1,1,1) -> "a", cons(q,List(2,2)) -> inject("b"), List(2,2,2) -> "c", List(3,2,2) -> "d")
        lookup(t,List(1,2,2),"b")
      }
    }
  }


}



trait TestGraphsBase extends FunSuite with Base with Engine with NatBase with ListBase with GraphBase with ReifyUtilsBase {

  test("graph") {

    val g = new Graph[String] {
      def edge(x:Exp[String],y:Exp[String]) = 
        (x === "a") && (y === "b") ||
        (x === "b") && (y === "c") ||
        (x === "c") && (y === "a")
    }

    expectResult(List(
      "pair(a,b)", "pair(b,c)", "pair(c,a)"
    )) {
      run[(String,String)] { case Pair(q1,q2) =>
        g.edge(q1,q2)
      }
    }
    expectResult(List(
      "b", "c", "a", "b", "c", "a", "b", "c", "a", "b"
    )) {
      runN[String](10) { q =>
        g.path("a",q)
      }
    }
  }

  test("trace") {
    val traceG = new Graph[String] {
      def edge(x:Exp[String],y:Exp[String]) = 
        (x === "a") && (y === "b") ||
        (x === "b") && (y === "c") ||
        (x === "c") && (y === "a")

      override def path(x:Exp[String],y:Exp[String]) = rule("path")(super.path)(x,y)
    }

    expectResult(List(
      "pair(b,cons(path(a,b),nil))", 
      "pair(c,cons(path(b,c),cons(path(a,c),nil)))", 
      "pair(a,cons(path(c,a),cons(path(b,a),cons(path(a,a),nil))))", 
      "pair(b,cons(path(a,b),cons(path(c,b),cons(path(b,b),cons(path(a,b),nil)))))", 
      "pair(c,cons(path(b,c),cons(path(a,c),cons(path(c,c),cons(path(b,c),cons(path(a,c),nil))))))"
    )) {
      runN[(String,List[String])](5) { case Pair(q1,q2) =>
        traceG.path("a",q1) && globalTrace() === q2
      }
    }
  }

}

class TestGraphs extends TestGraphsBase with ReifyUtils

class TestGraphsDynVars extends TestGraphsBase with ReifyUtilsDynVars


class TestMetaGraphs extends FunSuite with Base with Engine with MetaGraphBase {

  test("meta graph") {

    val g = new Graph[String] {
      def edge(x:Exp[String],y:Exp[String]) = 
        (x === "a") && (y === "b") ||
        (x === "b") && (y === "c") ||
        (x === "c") && (y === "a")
    }

    expectResult(List(
      "cons(to prove,cons(path(a,b),cons(prove,cons(nil,nil))))", 
      "cons(to prove,cons(path(b,c),cons(prove,cons(nil,nil))))", 
      "cons(to prove,cons(path(c,a),cons(prove,cons(nil,nil))))", 
      "cons(to prove,cons(path(a,x0),cons(prove,cons(path(b,x0),nil))))", 
      "cons(to prove,cons(path(b,x0),cons(prove,cons(path(c,x0),nil))))", 
      "cons(to prove,cons(path(c,x0),cons(prove,cons(path(a,x0),nil))))"
    )) {
      run[List[Any]] { q =>
        exists[Any,List[Any]] { (head,body) =>
          q === cons("to prove", cons(head, cons("prove", cons(body, nil)))) && 
          pathClause1(g)(head,body)
        }
      }
    }

    expectResult(List(
      "cons(to prove,cons(path(a,b),cons(prove,cons(nil,nil))))", 
      "cons(to prove,cons(path(b,c),cons(prove,cons(nil,nil))))", 
      "cons(to prove,cons(path(c,a),cons(prove,cons(nil,nil))))", 
      "cons(to prove,cons(path(a,x0),cons(prove,cons(path(b,x0),nil))))", 
      "cons(to prove,cons(path(b,x0),cons(prove,cons(path(c,x0),nil))))", 
      "cons(to prove,cons(path(c,x0),cons(prove,cons(path(a,x0),nil))))"
    )) {
      run[List[Any]] { q =>
        val clause = existsC[String,String] { (a,b) => pathClause2(g)(a,b) }        
        exists[Any,List[Any]] { (head,body) =>
          clause(head,body) && q === cons("to prove", cons(head, cons("prove", cons(body, nil))))
        }
      }
    }
  }


}

