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


trait ListBase extends InjectBase {
  implicit def injectList[T:Inject] = new Inject[List[T]] {
    def toTerm(x: List[T]): Exp[List[T]] = list(x:_*)
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
}

import org.scalatest._

class TestLists extends FunSuite with Base with Engine with Naturals with ListBase {

  def append[T](as: Exp[List[T]], bs: Exp[List[T]], cs: Exp[List[T]]): Rel =
    (as === nil && bs === cs) ||
    exists[T,List[T],List[T]] { (h,t1,t2) =>
      (as === cons(h,t1)) && (cs === cons(h,t2)) && append(t1,bs,t2)
    }

  def map[T,U](f: (Exp[T],Exp[U]) => Rel, as: Exp[List[T]], bs: Exp[List[U]]): Rel =
    (as === nil) && (bs === nil) ||
    exists[T,U,List[T],List[U]] { (a,b,as1,bs1) =>
      (as === cons(a,as1)) && (f(a,b) && (bs === cons(b,bs1)) && map[T,U](f,as1,bs1))
    }

  def flatMap[T,U](f: (Exp[T],Exp[List[U]]) => Rel, as: Exp[List[T]], cs: Exp[List[U]]): Rel =
    (as === nil) && (cs === nil) ||
    exists[T,List[U],List[T],List[U]] { (a,bs,as1,cs1) =>
      (as === cons(a,as1)) && f(a,bs) && append(bs, cs1, cs) && flatMap[T,U](f,as1,cs1)
    }


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

}

