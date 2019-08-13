package scalogno

import org.scalatest.{Engine => _, _}

trait TestTablingAppBase extends MySuite with ListBase with NatBase with TablingBase with Engine {
  def exp(s0: Exp[List[String]], s: Exp[List[String]]): Rel = memo(term("exp", List(s0,s))) {
    { val s1,s2 = fresh[List[String]]
      exp(s0,s1) && (s1 === cons("+",s2)) && trm(s2,s) } ||
    trm(s0, s) }
  def trm(s0: Exp[List[String]], s: Exp[List[String]]): Rel = memo(term("trm", List(s0,s))) {
    { val s1,s2 = fresh[List[String]]
      trm(s0,s1) && (s1 === cons("*",s2)) && fct(s2,s) } ||
    fct(s0, s) }
  def fct(s0: Exp[List[String]], s: Exp[List[String]]) = memo(term("fct", List(s0,s))) {
    { val s1,s2 = fresh[List[String]]
      s0 === cons("(", s1) && exp(s1, s2) && s2 === cons(")", s) } ||
    { val n = fresh[String]
      s0 === cons(n, s) && dgt(n) }
  }
  def dgt(n: Exp[String]) = memo(term("dgt",List(n))) {
    n === "0" || n === "1" || n === "2" || n === "3" || n === "4" ||
    n === "5" || n === "6" || n === "7" || n === "8" || n === "9"
  }

  def tokenize(s: String): List[String] = s.toList.map(_.toString)

  test("exp1") {
    expectResult(List()) {
      runN[List[String]](3) { q =>
        tabling(true)
        exp(tokenize("3+4*"),nil)
      }
    }
  }

  test("exp2") {
    expectResult(List("x0")) {
      runN[List[String]](3) { q =>
        tabling(true)
        exp(tokenize("3+4*5"),nil)
      }
    }
  }

  test("exp3") {
    expectResult(List("x0")) {
      runN[List[String]](3) { q =>
        tabling(true)
        exp(tokenize("(3+4)*7"),nil)
      }
    }
  }

  def list8(q: Exp[List[String]]): Rel = memo(term("list8", List(q))) {
      val x1 = fresh[String]
      val x2 = fresh[String]
      val x3 = fresh[String]
      val x4 = fresh[String]
      val x5 = fresh[String]
      val x6 = fresh[String]
      val x7 = fresh[String]
      val x8 = fresh[String]
      q === cons(x1,cons(x2,cons(x3,cons(x4,cons(x5,cons(x6,cons(x7,cons(x8, nil))))))))
  }

  test("exp4") {
    expectResult(List()) {
      runN[List[String]](3) { q =>
        tabling(true)
        list8(q) && exp(q,nil)
      }
    }
  }
}

class TestTablingApp extends TestTablingAppBase with TablingImpl

trait TestTablingBase extends MySuite with ListBase with NatBase with TablingBase with Engine {

  def fib(x:Exp[Int], y:Exp[Int]): Rel = memo(term("fib",List(x,y))) {
    (x === 0) && (y === 1) ||
    (x === 1) && (y === 1) || {
      val x1,x2,y1,y2 = fresh[Int]
      (x === succ(x1)) && (x === (succ(succ(x2)))) &&
      fib(x1,y1) && fib(x2,y2) &&
      add(y1,y2,y)
    }
  }

  test("fib1") {
    expectResult(List(
      "s(s(s(s(s(s(s(s(z))))))))"
    )) {
      runN[Int](3) { q =>
        tabling(false)
        fib(5,q)
      }
    }
    println("done")
  }

  test("fib2") {
    expectResult(List(
      "s(s(s(s(s(s(s(s(z))))))))"
    )) {
      runN[Int](3) { q =>
        tabling(true)
        fib(5,q)
      }
    }
    println("done")
  }
}

class TestTabling extends TestTablingBase with TablingImpl {

  def edge(x:Exp[String],y:Exp[String]) =
    (x === "a") && (y === "b") ||
    (x === "b") && (y === "c") ||
    (x === "c") && (y === "a")

  def pathL(a: Exp[String], b: Exp[String]): Rel = memo(term("path",List(a,b))) {
    edge(a,b) || exists[String] { z => pathL(a,z) && { println("--"+extractStr(term("path-edge",List(a,z,b)))); edge(z,b) } }
  }
  def pathR(a: Exp[String], b: Exp[String]): Rel = memo(term("path",List(a,b))) {
    edge(a,b) || exists[String] { z => edge(a,z) && pathR(z,b) }
  }

  val globalTrace = DVar(nil: Exp[List[List[String]]])

  def pathLT(a: Exp[String], b: Exp[String]): Rel = memo(term("path",List(a,b))) {
    globalTrace := cons(term("path",List(a,b)), globalTrace())
    edge(a,b) || exists[String] { z => pathLT(a,z) && { println("--"+extractStr(term("path-edge",List(a,z,b)))); edge(z,b) } }
  }
  def pathRT(a: Exp[String], b: Exp[String]): Rel = memo(term("path",List(a,b))) {
    globalTrace := cons(term("path",List(a,b)), globalTrace())
    edge(a,b) || exists[String] { z => edge(a,z) && pathRT(z,b) }
  }


  test("pathR") {
    expectResult(List(
      "b","c","a"
    )) {
      runN[String](5) { q1 =>
        tabling(true)
        pathR("a",q1)
      }
    }
    println("done")
  }

  test("pathL") {
    expectResult(List(
      "b","c","a"
    )) {
      runN[String](5) { q1 =>
        tabling(true)
        pathL("a",q1)
      }
    }
    println("done")
  }

  test("pathRT") {
    expectResult(List(
      "pair(b,cons(path(a,b),nil))",
      "pair(c,cons(path(b,c),cons(path(a,c),nil)))",
      "pair(a,cons(path(c,a),cons(path(b,a),cons(path(a,a),nil))))"
    )) {
      runN[(String,List[List[String]])](5) { case Pair(q1,q2) =>
        tabling(true)
        pathRT("a",q1) && globalTrace() === q2
      }
    }
    println("done")
  }

  test("pathLT") {
    expectResult(List(
      "pair(b,cons(path(a,b),nil))",
      "pair(c,cons(path(a,b),cons(path(a,c),nil)))",
      "pair(a,cons(path(a,b),cons(path(a,c),cons(path(a,a),nil))))"
    )) {
      runN[(String,List[List[String]])](5) { case Pair(q1,q2) =>
        tabling(true)
        pathLT("a",q1) && globalTrace() === q2
      }
    }
    println("done")
  }

}


class TestTablingMore extends MySuite with ListBase with NatBase with TablingImpl with Engine {

  val accum = DVar(nil: Exp[List[String]])
  def inc(n: Exp[Int]): Rel = {
    (n === 0) || exists[Int] { n1 =>
      (n === succ(n1)) && {
        accum := cons("A", accum())
        inc(n1)
      }
    }
  }

  def dlet[T](p: (DVar[T],T))(body: =>Rel): Rel = new Rel {
    override def exec(rec: Exec)(k: Cont): Unit = {
      val (v,x) = p
      val old = v()
      v := x
      rec(() => body) { () => v := old; k() }
    }
  }

  val last = DVar(nil: Exp[List[String]])
  def inc2(n: Exp[Int]): Rel = {
    (n === 0) && (accum() === last()) ||
    exists[Int] { n1 =>
      (n === succ(n1)) && exists[List[String]] { tail =>
        accum() === cons("A", tail) && dlet(accum -> tail) {
          inc2(n1)
        }
      }
    }
  }


  test("dletRel1") {
    expectResult(List(
      "pair(x0,cons(A,cons(A,cons(A,x0))))"
    )) {
      runN[(List[String],List[String])](5) { case Pair(q1,q2) =>
        tabling(false)
        dlet(last -> q1) {
          dlet(accum -> q2) {
            inc2(3)
          }
        }
      }
    }
  }


  test("stateRel1") {
    expectResult(List(
      "pair(x0,cons(A,cons(A,cons(A,x0))))"
    )) {
      runN[(List[String],List[String])](5) { case Pair(q1,q2) =>
        tabling(false)
        accum := q1
        inc(3) && accum() === q2
      }
    }
  }

  test("stateRel2") {
    expectResult(List(
      "pair(z,pair(x0,x0))",
      "pair(s(z),pair(x0,cons(A,x0)))",
      "pair(s(s(z)),pair(x0,cons(A,cons(A,x0))))",
      "pair(s(s(s(z))),pair(x0,cons(A,cons(A,cons(A,x0)))))",
      "pair(s(s(s(s(z)))),pair(x0,cons(A,cons(A,cons(A,cons(A,x0))))))"
    )) {
      runN[(Int,(List[String],List[String]))](5) { case Pair(q1,Pair(q2,q3)) =>
        tabling(false)
        accum := q2
        inc(q1) && accum() === q3
      }
    }
  }

  test("stateRel3") {
    expectResult(List(
      "pair(z,cons(A,cons(A,cons(A,cons(A,nil)))))",
      "pair(s(z),cons(A,cons(A,cons(A,nil))))",
      "pair(s(s(z)),cons(A,cons(A,nil)))",
      "pair(s(s(s(z))),cons(A,nil))",
      "pair(s(s(s(s(z)))),nil)"
    )) {
      runN[(Int,List[String])](5) { case Pair(q1,q2) =>
        tabling(false)
        accum := q2
        inc(q1) && accum() === List("A","A","A","A")
      }
    }
  }


  test("stateRel1T") {
    expectResult(List(
      "pair(x0,cons(A,cons(A,cons(A,x0))))"
    )) {
      runN[(List[String],List[String])](5) { case Pair(q1,q2) =>
        tabling(true)
        accum := q1
        inc(3) && accum() === q2
      }
    }
  }

  test("stateRel2T") {
    expectResult(List(
      "pair(z,pair(x0,x0))",
      "pair(s(z),pair(x0,cons(A,x0)))",
      "pair(s(s(z)),pair(x0,cons(A,cons(A,x0))))",
      "pair(s(s(s(z))),pair(x0,cons(A,cons(A,cons(A,x0)))))",
      "pair(s(s(s(s(z)))),pair(x0,cons(A,cons(A,cons(A,cons(A,x0))))))"
    )) {
      runN[(Int,(List[String],List[String]))](5) { case Pair(q1,Pair(q2,q3)) =>
        tabling(true)
        accum := q2
        inc(q1) && accum() === q3
      }
    }
  }

  test("stateRel3T") {
    expectResult(List(
      "pair(z,cons(A,cons(A,cons(A,cons(A,nil)))))",
      "pair(s(z),cons(A,cons(A,cons(A,nil))))",
      "pair(s(s(z)),cons(A,cons(A,nil)))",
      "pair(s(s(s(z))),cons(A,nil))",
      "pair(s(s(s(s(z)))),nil)"
    )) {
      runN[(Int,List[String])](5) { case Pair(q1,q2) =>
        tabling(true)
        accum := q2
        inc(q1) && accum() === List("A","A","A","A")
      }
    }
  }
}
