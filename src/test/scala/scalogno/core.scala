package scalogno

import org.scalatest._

class MySuite extends FunSuite {
  def expectResult(expected: Object)(actual: Object) = {
    assert(expected == actual)
  }
}

class TestNats extends MySuite with Base with Engine with NatBase with ListBase {

  test("lte") {
    // ASK(Tiark): why is there only 4 in the result. What about 5, 6, 7...?
    expectResult(List("s(s(s(s(x0))))")) {
      run[Int] { q =>
        lessThan(3, q)
      }
    }
  }

}

class TestLists extends MySuite with Base with Engine with NatBase with ListBase {

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
        map[String,String]((u,v) => u === v, list("a","b","c","d","e","f"), q)

      }
    }
    expectResult(List("cons(A,cons(B,cons(C,cons(A,cons(B,cons(C,nil))))))")) {
      run[List[String]] { q =>
        val elems = (List("a","b","c","d","e","f") zip List("A","B","C","A","B","C")): Exp[List[(String,String)]]
        map[String,String]((u,v) => contains(elems,(u,v)), list("a","b","c","d","e","f"), q)
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
        val elems = (List("a","b","c","d","e","f") zip List("A","B","C","A","B","C")): Exp[List[(String,String)]]
        map[String,String]((u,v) => contains(elems,(u,v)), q, list("A","B","A"))
      }
    }
  }

  /*
  test("mapf") {
    try {
      //delayedMode = true

      expectResult(List("cons(a,cons(b,cons(c,cons(d,cons(e,cons(f,nil))))))")) {
        run[List[String]] { q =>
          val res = mapf[String,String](list("a","b","c","d","e","f"), (u,v) => u === v)
          q === res
        }
      }
      expectResult(List("cons(A,cons(B,cons(C,cons(A,cons(B,cons(C,nil))))))")) {
        run[List[String]] { q =>
          val elems = (List("a","b","c","d","e","f") zip List("A","B","C","A","B","C")): Exp[List[(String,String)]]
          val res = mapf[String,String](list("a","b","c","d","e","f"), (u,v) => contains(elems,(u,v)))
          q === res
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
          val elems = (List("a","b","c","d","e","f") zip List("A","B","C","A","B","C")): Exp[List[(String,String)]]
          val res = mapf[String,String](q, (u,v) => contains(elems,(u,v)))
          res === list("A","B","A")
        }
      }

    } finally {
      //delayedMode = false
    }
  }
  */

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

class TestTrees extends MySuite with Base with Engine with NatBase with ListBase with TreeBase {

  test("tree") {
    expectResult(List(
      "branch(branch(branch(nil,s(z),a,nil),s(s(z)),b,nil),s(s(s(z))),c,branch(nil,s(s(s(s(z)))),d,nil))"
    )) {
      run[Tree[Int,String]] { q =>
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


trait TestGraphsBase extends MySuite with Base with Engine with NatBase with ListBase with GraphBase with ReifyUtilsBase {

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
      runN[(String,List[List[String]])](5) { case Pair(q1,q2) =>
        traceG.path("a",q1) && globalTrace() === q2
      }
    }
  }

}

class TestGraphs extends TestGraphsBase with ReifyUtils

class TestGraphsDynVars extends TestGraphsBase with ReifyUtilsDynVars


class TestMetaGraphs extends MySuite with Base with Engine with MetaGraphBase {

  val g = new Graph[String] {
    def edge(x:Exp[String],y:Exp[String]) =
      (x === "a") && (y === "b") ||
      (x === "b") && (y === "c") ||
      (x === "c") && (y === "a")
  }

  test("meta graph") {

    expectResult(List(
      "cons(to prove,cons(path(x0,x1),cons(prove,cons(cons(edge(x0,x1),nil),nil))))",
      "cons(to prove,cons(path(x0,x1),cons(prove,cons(cons(edge(x0,x2),cons(path(x2,x1),nil)),nil))))"
    )) {
      run[List[Any]] { q =>
        exists[Goal,List[Goal]] { (head,body) =>
          exists[String,String] { (a,b) => pathTerm(a,b) === head } &&
          q === cons("to prove", cons(head, cons("prove", cons(body, nil)))) &&
          pathFullClause1(g)(head,body)
        }
      }
    }

    expectResult(List(
      "cons(to prove,cons(path(a,b),cons(prove,cons(nil,nil))))",
      "cons(to prove,cons(path(b,c),cons(prove,cons(nil,nil))))",
      "cons(to prove,cons(path(c,a),cons(prove,cons(nil,nil))))",
      "cons(to prove,cons(path(a,x0),cons(prove,cons(cons(path(b,x0),nil),nil))))",
      "cons(to prove,cons(path(b,x0),cons(prove,cons(cons(path(c,x0),nil),nil))))",
      "cons(to prove,cons(path(c,x0),cons(prove,cons(cons(path(a,x0),nil),nil))))"
    )) {
      run[List[Any]] { q =>
        exists[Goal,List[Goal]] { (head,body) =>
          q === cons("to prove", cons(head, cons("prove", cons(body, nil)))) &&
          pathClause1(g)(head,body)
        }
      }
    }

    expectResult(List(
      "cons(to prove,cons(path(a,b),cons(prove,cons(nil,nil))))",
      "cons(to prove,cons(path(b,c),cons(prove,cons(nil,nil))))",
      "cons(to prove,cons(path(c,a),cons(prove,cons(nil,nil))))",
      "cons(to prove,cons(path(a,x0),cons(prove,cons(cons(path(b,x0),nil),nil))))",
      "cons(to prove,cons(path(b,x0),cons(prove,cons(cons(path(c,x0),nil),nil))))",
      "cons(to prove,cons(path(c,x0),cons(prove,cons(cons(path(a,x0),nil),nil))))"
    )) {
      run[List[Any]] { q =>
        val clause = existsC[String,String] { (a,b) => pathClause2(g)(a,b) }
        exists[Goal,List[Goal]] { (head,body) =>
          clause(head,body) && q === cons("to prove", cons(head, cons("prove", cons(body, nil))))
        }
      }
    }

    expectResult(List(
      "cons(to prove,cons(path(a,b),cons(prove,cons(nil,nil))))",
      "cons(to prove,cons(path(b,c),cons(prove,cons(nil,nil))))",
      "cons(to prove,cons(path(c,a),cons(prove,cons(nil,nil))))",
      "cons(to prove,cons(path(a,x0),cons(prove,cons(cons(path(b,x0),nil),nil))))",
      "cons(to prove,cons(path(b,x0),cons(prove,cons(cons(path(c,x0),nil),nil))))",
      "cons(to prove,cons(path(c,x0),cons(prove,cons(cons(path(a,x0),nil),nil))))"
    )) {
      run[List[Any]] { q =>
        exists[Goal,List[Goal]] { (head,body) =>
          q === cons("to prove", cons(head, cons("prove", cons(body, nil)))) &&
          reifyClause(path2(g)(fresh,fresh))(head,body)
        }
      }
    }

  }


  test("graph interp") {

    expectResult(List(
      "b", "c", "a", "b", "c", "a", "b", "c", "a", "b"
    )) {
      runN[List[Any]](10) { q =>
        vanilla(pathClause1(g))(cons(pathTerm("a",q),nil))
      }
    }

    expectResult(List(
        "pair(b,cons(path(a,b),nil))",
        "pair(c,cons(path(b,c),cons(path(a,c),nil)))",
        "pair(a,cons(path(c,a),cons(path(b,a),cons(path(a,a),nil))))",
        "pair(b,cons(path(a,b),cons(path(c,b),cons(path(b,b),cons(path(a,b),nil)))))"
    )) {
      runN[(List[Any],List[Goal])](4) { case Pair(q,t) =>
        tracer(pathClause1(g))(nil,t)(cons(pathTerm("a",q),nil))
      }
    }

  }

  test("graph interp2") {

    expectResult(List(
      "b", "c", "a", "b", "c", "a", "b", "c", "a", "b"
    )) {
      runN[String](10) { q =>
        vanilla2(path2(g)("a",q))
      }
    }

  }


}



class TestSTLC extends MySuite with Base with Engine with STLC with STLC_ReverseDeBruijn with STLC_Nat {

  test("stlc1") {
    expectResult(List(
      "pair(cons(x0,nil),pair(z,x0))",
      "pair(cons(x0,cons(x1,nil)),pair(s(z),x0))",
      "pair(cons(x0,cons(x1,cons(x2,nil))),pair(s(s(z)),x0))"
    )) {
      runN[(Env,(Sym,LType))](3) { case Pair(g,Pair(x,tp)) =>
        lookup(g,x,tp)
      }
    }

    expectResult(List(
      "pair(cons(x0,nil),pair(z,x0))",
      "pair(cons(x0,cons(x1,nil)),pair(s(z),x0))",
      "pair(cons(x0,cons(x1,cons(x2,nil))),pair(s(s(z)),x0))"
    )) {
      runN[(Env,(Sym,LType))](3) { case Pair(g,Pair(x,tp)) =>
        val d1 = g |- sym(x) :: tp
        typecheck(d1)
      }
    }

    expectResult(List(
      "|-(cons(x0,cons(->(x0,x1),nil)),@(var(z),var(s(z))),x1)",
      "|-(cons(x0,cons(x1,cons(->(x1,x2),nil))),@(var(z),var(s(z))),x2)",
      "|-(cons(x0,cons(x1,cons(x2,cons(->(x2,x3),nil)))),@(var(z),var(s(z))),x3)"
    )) {
      runN[Deriv](3) { d =>
        val a = fresh[Env] |- (sym(0) app sym(1)) :: fresh[LType]
        d === a && typecheck(d)
      }
    }

    expectResult(List(
      "|-(nil,lam(z,lam(s(z),@(var(z),var(s(z))))),->(->(x0,x1),->(x0,x1)))"
    )) {
      runN[Deriv](3) { d =>
        val x,y = fresh[Sym]
        val a = nil |- lam(x, lam(y, (sym(x) app sym(y)))) :: fresh[LType]
        d === a && typecheck(d)
      }
    }

    expectResult(List(
      "|-(nil,lam(z,lam(s(z),+(var(z),var(s(z))))),->(nat,->(nat,nat)))"
    )) {
      runN[Deriv](3) { d =>
        val x,y = fresh[Sym]
        val a = nil |- lam(x, lam(y, (sym(x) + sym(y)))) :: fresh[LType]
        d === a && typecheck(d)
      }
    }

  }
}


class TestXX extends MySuite with ListBase with NatBase with Engine with MetaGraphBase {

  trait LF

  val typ = term[LF]("type",Nil)

  def lf(x:Exp[LF],y:Exp[LF]) = term[Goal]("lf",List(x,y))

  val nat = term[LF]("nat",Nil)

  val z = term[LF]("z",Nil)

  def s(x:Exp[LF]) = term[LF]("s",List(x))

  def lte(x:Exp[LF],y:Exp[LF]) = term[LF]("lte",List(x,y))

  def lte_z = term[LF]("lte_z",Nil)
  def lte_s(x:Exp[LF]) = term[LF]("lte_s",List(x))

  def clauses(head: Exp[Goal], body: Exp[List[Goal]]): Rel =
    (head === lf(nat,typ)) && (body === nil) || // nat
    (head === lf(z,nat))   && (body === nil) ||
    exists[LF] { x =>
      (head === lf(s(x),nat)) && (body === cons(lf(x,nat),nil))
    } || // lte
    exists[LF,LF] { (x,y) =>
      (head === lf(lte(x,y),typ)) && (body === cons(lf(x,nat),cons(lf(y,nat),nil)))
    } ||
    exists[LF,LF] { (x,y) =>
      (head === lf(lte_z,lte(z,x))) && (body === nil)
    } ||
    exists[LF,LF,LF] { (x,y,u) =>
      (head === lf(lte_s(u),lte(s(x),s(y)))) && (body === cons(lf(u,lte(x,y)),nil))
    }

/*
lte-trans : lte A B -> lte B C -> lte A C -> type.
%mode lte-trans +A +B -C.

-/z : lte-trans lte/z B lte/z.
-/s : lte-trans (lte/s A) (lte/s B) (lte/s C)
     <- lte-trans A B C.

%worlds () (lte-trans _ _ _).
%total A (lte-trans A _ _).
*/

  test("clause interp") {

    expectResult(List(
      "z", "s(z)", "s(s(z))"
    )) {
      runN[LF](3) { q =>
        vanilla(clauses)(cons(lf(q,nat),nil))
      }
    }

    expectResult(List(
      "pair(lte_s(lte_s(lte_z)),s(s(x0)))"
    )) {
      runN[(LF,LF)](3) { case Pair(q,n) =>
        vanilla(clauses)(cons(lf(q,lte(s(s(z)),n)),nil))
      }
    }


  }



}


class TestProb extends MySuite with ListBase with NatBase with Engine {

  implicit val injectBool = new Inject[Boolean] {
    def toTerm(x: Boolean): Exp[Boolean] = term(x.toString,Nil)
  }
  implicit val injectDouble = new Inject[Double] {
    def toTerm(x: Double): Exp[Double] = term(x.toString,Nil)
  }

  val theprob = DVar(1.0)

  def flip(p: Double, x: Exp[Boolean]): Rel =
    { theprob := theprob() * p; x === true } ||
    { theprob := theprob() * (1.0 - p); x === false }

  def flip2(p: Double)(a: => Rel)(b: => Rel): Rel =
    { theprob := theprob() * p; a } ||
    { theprob := theprob() * (1.0 - p); b }


  test("prob1") {

    expectResult(List(
      "pair(true,0.2)",
      "pair(false,0.8)"
    )) {
      runN[(Boolean,Double)](3) { case Pair(c,p) =>
        flip(0.2,c) && { p === theprob() }
      }
    }

    expectResult(List(
      s"pair(true,${1.0*0.2*0.2})"
    )) {
      runN[(Boolean,Double)](3) { case Pair(c,p) =>
        // what about call-time choice???
        flip(0.2,c) && flip(0.2,c) && { c === true } && { p === theprob() }
      }
    }

    expectResult(List(
      "pair(true,0.2)"
    )) {
      runN[(Boolean,Double)](3) { case Pair(c,p) =>
        flip2(0.2) { c === true } { c === false } && { c === true } && { p === theprob() }
      }
    }

  }

}
