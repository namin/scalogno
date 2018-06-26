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

  def add(a: Exp[Int], b: Exp[Int], c: Exp[Int]): Rel =
    (a === zero) && (b === c) ||
    exists[Int,Int] { (a1,c1) =>
      (a === succ(a1)) && (c === succ(c1)) && add(a1,b,c1)
    }

}




trait ListBase extends InjectBase with Ordering {
  implicit def injectPair[T:Inject,U:Inject] = new Inject[(T,U)] {
    def toTerm(x: (T,U)): Exp[(T,U)] = pair(x._1,x._2)
  }
  implicit def injectList[T:Inject] = new Inject[List[T]] {
    def toTerm(x: List[T]): Exp[List[T]] = list(x:_*)
  }
  implicit def ordList[T:Ord] = new Ord[List[T]] {
    def lt(x:Exp[List[T]],y:Exp[List[T]]): Rel = lessLex[T]((a1,a2) => a1 < a2, x,y)
  }

  implicit def injectPairShallow[T,U](x: (Exp[T],Exp[U])) = pair(x._1,x._2)
  implicit def injectListShallow[T](xs: List[Exp[T]]): Exp[List[T]] = if (xs.isEmpty) nil else cons(xs.head,xs.tail)


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


  def contains[T](xs: Exp[List[T]], y:Exp[T]): Rel =
    exists[T,List[T]] { (x,xs1) =>
      xs === cons(x,xs1) && (x === y || contains(xs1,y))
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

  def mapf[T,U](as: Exp[List[T]], f: (Exp[T],Exp[U]) => Rel): Exp[List[U]] = {
    val bs = fresh[List[U]]
    map(f,as,bs) // needs delayed mode
    bs
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

trait MetaGraphBase extends GraphBase with ListBase with Engine with MetaVanilla with MetaReifyVanilla with MetaTracer {

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

  def pathTerm[T](a: Exp[T], b: Exp[T]) = term[Goal]("path",List(a,b))

  def pathClause1[T](g: Graph[T])(head: Exp[Goal], body: Exp[List[Goal]]) = {
    exists[T,T] { (a,b) =>
      (head === pathTerm(a,b)) && {
        (g.edge(a,b) && (body === nil)) ||
        exists[T] { z =>
          g.edge(a,z) && (body === cons(pathTerm(z,b),nil))
        }
      }
    }
  }

  def edgeTerm[T](a: Exp[T], b: Exp[T]) = term[Goal]("edge",List(a,b))

  def pathFullClause1[T](g: Graph[T])(head: Exp[Goal], body: Exp[List[Goal]]) = {
    exists[T,T] { (a,b) =>
      ((head === pathTerm(a,b)) && (
        (body === cons(edgeTerm(a,b),nil)) ||
          exists[T] { z =>
            body === cons(edgeTerm(a,z), cons(pathTerm(z,b),nil))
          }
      )) ||
      ((head === edgeTerm(a,b)) && g.edge(a,b))
    }
  }

/*
(run 10 (q)
  ((vanilla* patho-clause)
   ‘((patho a ,q)))) => (b c a b c a b c a b)
*/

  def pathClause2[T](g: Graph[T])(a: Exp[T], b: Exp[T]) = { (head: Exp[Goal], body: Exp[List[Goal]]) =>
    (head === pathTerm(a,b)) && {
      g.edge(a,b) && (body === nil) ||
      exists[T] { z =>
        g.edge(a,z) && (body === cons(pathTerm(z,b),nil))
      }
    }
  }

  def path2[T](g: Graph[T]): (Exp[T],Exp[T])=> Rel =
    rule("path"/*+g.toString*/) { (a,b) =>
      g.edge(a,b) ||
      exists[T] { z =>
        g.edge(a,z) && path2(g)(z,b)
      }
    }
}


trait ReifyUtilsBase extends Base with InjectBase with ListBase with Engine {
  def rule[T,U](s: String)(f: (Exp[T],Exp[U]) => Rel): (Exp[T],Exp[U]) => Rel
  def globalTrace: () => Exp[List[List[String]]]
}

trait ReifyUtilsDynVars extends ReifyUtilsBase with InjectBase with ListBase with Engine {
  val _globalTrace = DVar(nil: Exp[List[List[String]]])
  override def globalTrace = () => _globalTrace()

  def rule[T,U](s: String)(f: (Exp[T],Exp[U]) => Rel): (Exp[T],Exp[U]) => Rel =
    { (a,b) =>
      _globalTrace := cons(term(s,List(a,b)), _globalTrace())
      f(a,b)
    }
}

trait ReifyUtils extends ReifyUtilsBase with InjectBase with ListBase with Engine {

  var globalTrace0: Exp[List[List[String]]] = nil

  def globalTrace = () => globalTrace0
  def globalTrace_=(x:Exp[List[List[String]]]) = globalTrace0 = x

  def rule[T,U](s: String)(f: (Exp[T],Exp[U]) => Rel): (Exp[T],Exp[U]) => Rel =
    { (a,b) =>
      globalTrace = cons(term(s,List(a,b)),globalTrace());
      f(a,b)
    }
}



trait STLC extends Base with InjectBase with ListBase with Engine {

  trait LTerm
  trait LType
  trait Deriv
  trait Rule

  type Sym
  type Env

  implicit class EnvOps(x: Exp[Env]) {
    def |- (y: (Exp[LTerm],Exp[LType])) = term[Deriv]("|-", List(x,y._1,y._2))
  }

  implicit class TypeOps(x: Exp[LType]) {
    def :: (e: Exp[LTerm]) = (e,x)
    def -> (y: Exp[LType]) = term[LType]("->", List(x,y))
  }

  implicit class TermOps(x: Exp[LTerm]) {
    def app(y: Exp[LTerm]) = term[LTerm]("@", List(x,y))
  }

  def sym(x: Exp[Sym]) = term[LTerm]("var", List(x))

  def lam(x: Exp[Sym], y: Exp[LTerm]) = term[LTerm]("lam", List(x,y))

  // judgments

  def extend(g: Exp[Env], x: Exp[Sym], tp: Exp[LType], g1: Exp[Env]): Rel

  def lookup(g: Exp[Env], x: Exp[Sym], tp: Exp[LType]): Rel

  def typecheck(d: Exp[Deriv]): Rel =
    exists[Env,Sym,LType] { (G,x,t1) =>
      val a = G |- sym(x) :: t1

      d === a && lookup(G,x,t1)
    } ||
    exists[Env,Env,Sym,LTerm,LType,LType] { (G,G1,x,e,t1,t2) =>
      val a = G |- lam(x,e) :: (t1 -> t2)
      val b = G1 |- e :: t2

      d === a && extend(G,x,t1,G1) && typecheck(b)
    } ||
    exists[Env,LTerm,LTerm,LType,LType] { (G,e1,e2,t1,t2) =>
      val a = G |- (e1 app e2) :: t2
      val b = G |- e1 :: (t1 -> t2)
      val c = G |- e2 :: t1

      d === a && typecheck(b) && typecheck(c)
    }
}

trait STLC_ReverseDeBruijn extends STLC with NatBase {

  // env is list of types, indexed by int

  type Sym = Int
  type Env = List[LType]

  def extend(g: Exp[Env], x: Exp[Sym], tp: Exp[LType], g1: Exp[Env]): Rel =
    g1 === cons(tp,g) && freein(g,x)


  def lookup(g: Exp[Env], x: Exp[Sym], tp: Exp[LType]): Rel =
    exists[LType,Env] { (hd,tl) =>
      g === cons(hd,tl) && {
        freein(tl,x) && (hd === tp) ||
        lookup(tl,x,tp)
      }
    }

  def freein(g: Exp[Env], x: Exp[Sym]): Rel =
    g === nil && x === zero ||
    exists[Sym,Env] { (x1,tl) =>
      g === cons(fresh[LType],tl) && x === succ(x1) && freein(tl,x1)
    }
}

trait STLC_Nat extends STLC {

  implicit class NatTermOps(x: Exp[LTerm]) {
    def +(y: Exp[LTerm]) = term[LTerm]("+", List(x,y))
  }

  def tnat = term[LType]("nat",Nil)

  def cnat(x: Exp[Int]) = term[LTerm]("nat",List(x))

  override def typecheck(d: Exp[Deriv]): Rel =
    exists[Env,Int] { (G,x) =>
      val a = G |- cnat(x) :: tnat

      d === a
    } ||
    exists[Env,LTerm,LTerm] { (G,e1,e2) =>
      val a = G |- (e1 + e2) :: tnat
      val b = G |- e1 :: tnat
      val c = G |- e2 :: tnat

      d === a && typecheck(b) && typecheck(c)
    } ||
    super.typecheck(d)

}
