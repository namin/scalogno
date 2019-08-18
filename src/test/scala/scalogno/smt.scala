package scalogno

import org.scalatest.{Engine => _, _}

class TestExe extends MySuite with Engine {
  test("1") {
    solver.init()
    solver.smt.write("(assert (= 1 0))")
    solver.smt.write("(check-sat)")
    expectResult("unsat") { solver.smt.readAtom() }
    solver.smt.close()
  }

  test("2debug") {
    solver.init()
    solver.smt.write("(declare-const x0 Int)")
    solver.smt.write("(assert (= 1 x0))")
    solver.smt.write("(check-sat)")
    expectResult("sat") { solver.smt.readAtom() }
    solver.smt.write("(get-model)")
    val s = solver.smt.readSExp()
    //println(s)
    val p = raw"\(define-fun x([0-9]+) \(\) Int ([0-9]+)\)".r
    for (m <- p.findAllMatchIn(s)) {
      val id = m.group(1).toInt
      val v = m.group(2).toInt
      //println(s"$id has $v")
    }
  }

  test("2") {
    solver.init()
    solver.smt.write("(declare-const x0 Int)")
    solver.smt.write("(assert (= 1 x0))")
    solver.smt.write("(check-sat)")
    expectResult("sat") { solver.smt.readAtom() }
    var ms: List[(Int,Int)] = Nil
    solver.extractModel((k,v) => ms = (k,v)::ms)
    expectResult(List((0,1)))(ms)
    solver.smt.close()
  }
}

class TestSmt extends MySuite with Smt with Engine {
 test("0") {
    expectResult(Nil) {
      run[Int] { q =>
        A(0) ==? A(1)
      }
    }
  }
  test("1") {
    expectResult(Nil) {
      run[Int] { q =>
        q ==? 1 &&
        q ==? 0
      }
    }
  }
  test("2") {
    expectResult(List("1")) {
      run[Int] { q =>
        q ==? 1
      }
    }
  }
}

class TestFactorial extends MySuite with Smt with Engine {
  def faco(n: Exp[Int], o: Exp[Int]): Rel =
    (n >= 0) &&
    (
      (n ==? 0) && (o ==? 1) ||

      exists[Int,Int]{(n1,r) =>
        (n - 1) ==? n1 &&
          (n * r) ==? o &&
        faco(n1, r)
      }
    )

  test("7") {
    expectResult(List("1", "1", "2", "6", "24", "120", "720")) {
      runN[Int](7){ o => exists[Int]{n => faco(n,o)} }
    }
  }

  test("only 6") {
    expectResult(List("720")) {
      runN[Int](6){ o => faco(6,o) }
    }
  }
}

class TestFib extends MySuite with Smt with Engine {
  def fibo(n: Exp[Int], o: Exp[Int]): Rel =
    ((n ==? 0) && (o ==? 1)) ||
    ((n ==? 1) && (o ==? 2)) ||
    { val n1,n2,o1,o2 = fresh[Int]
      (n > 1) &&
      (n1 ==? (n - 1)) &&
      (n2 ==? (n - 2)) &&
      (o ==? o1 + o2) &&
      fibo(n2, o2) &&
      fibo(n1, o1) }

  test("6") {
    expectResult(List("1", "2", "3", "5", "8", "13")) {
      runN[Int](6){ o => exists[Int]{n => fibo(n,o)} }
    }
  }
}

class TestSmtTab extends MySuite with Smt with Engine with ListBase with TablingBase with TablingImpl {
  def fibo(n: Exp[Int], o: Exp[Int]): Rel = memo(term("fibo", List(n,o))) {
    ((n ==? 0) && (o ==? 1)) ||
    ((n ==? 1) && (o ==? 2)) ||
    { val n1,n2,o1,o2 = fresh[Int]
      (n > 1) &&
      (n1 ==? (n - 1)) &&
      (n2 ==? (n - 2)) &&
      fibo(n2, o2) &&
      fibo(n1, o1) &&
      (o ==? o1 + o2) }

  }

  def faco(n: Exp[Int], o: Exp[Int]): Rel = memo(term("faco", List(n,o))) {
    (n >= 0) &&
    (
      (n ==? 0) && (o ==? 1) ||

      exists[Int,Int]{(n1,r) =>
        (n - 1) ==? n1 &&
        faco(n1, r) &&
        (n * r) ==? o
      }
    )
  }

  test("faco 7") {
    tabling(true)
    expectResult(List("1", "1", "2", "6", "24", "120", "720")) {
      runN[Int](7){ o => exists[Int]{n => faco(n,o)}
      }
    }
  }

  test("faco only 6") {
    tabling(true)
    expectResult(List("720")) {
      runN[Int](6){ o =>
        faco(6,o)
      }
    }
  }

  test("fibo 5") {
    tabling(true)
    expectResult(List("1", "2", "3", "5", "8")) {
      runN[Int](5){ o =>
        exists[Int]{n => fibo(n,o)}
      }
    }
  }

  test("fibo only 3") {
    tabling(true)
    expectResult(List("5")) {
      runN[Int](6){ o =>
        fibo(3,o)
      }
    }
  }
}

class TestSmtTabGraph extends MySuite with Smt with Engine with ListBase with TablingBase with TablingImpl {

  def edge(x:Exp[String],y:Exp[String],c:Exp[Int]) =
    (x === "a") && (y === "b") && (c ==? 1) ||
    (x === "b") && (y === "c") && (c ==? 1) ||
    (x === "c") && (y === "a") && (c ==? 1)

  def memoShortestPath(a: Exp[String], b: Exp[String], c: Exp[Int])(r: => Rel): Rel = memo(term("path",List(a,b,c)), { x => (cstore collect { case IsTerm(id, k , List(a,b,_)) if id==x.id => term(k, List(a,b)) }).head })(r)

  def pathL(a: Exp[String], b: Exp[String], c: Exp[Int]): Rel = memoShortestPath(a, b, c) {
    edge(a,b,c) || exists[String] { z => exists[Int] { c1 => pathL(a,z,c1) && exists[Int] { c2 => { println("--"+extractStr(term("path-edge",List(a,z,b)))); edge(z,b,c2) && c1+c2 ==? c
    }}}}}

  def pathR(a: Exp[String], b: Exp[String], c: Exp[Int]): Rel = memoShortestPath(a, b, c) {
    edge(a,b,c) || exists[String] { z => val c1,c2 = fresh[Int]; edge(a,z,c1) && pathR(z,b,c2) && c1 + c2 ==? c
    }}

  val globalTrace = DVar(nil: Exp[List[List[String]]])

  def pathLT(a: Exp[String], b: Exp[String], c: Exp[Int]): Rel = memoShortestPath(a, b, c) {
    globalTrace := cons(term("path",List(a,b,c)), globalTrace())
    edge(a,b,c) || exists[String] { z => exists[Int] { c1 => pathLT(a,z,c1) && exists[Int] { c2 => { println("--"+extractStr(term("path-edge",List(a,z,b)))); edge(z,b,c2) && c1+c2 ==? c
  }}}}}
  def pathRT(a: Exp[String], b: Exp[String], c: Exp[Int]): Rel = memoShortestPath(a, b, c) {
    globalTrace := cons(term("path",List(a,b,c)), globalTrace())
    edge(a,b,c) || exists[String] { z => val c1,c2 = fresh[Int]; edge(a,z,c1) && pathRT(z,b,c2) && c1 + c2 ==? c
  }}

  test("pathR") {
    expectResult(List(
      "cons(b,1)","cons(c,2)","cons(a,3)"
    )) {
      tabling(true)
      runN[String](5) { q =>
        val b, c = fresh[Int]
        q === cons(b,c) &&
        pathR("a",b,c)
      }
    }
    println("done")
  }

  test("pathL") {
    expectResult(List(
      "cons(b,1)","cons(c,2)","cons(a,3)"
    )) {
      runN[String](5) { q =>
        tabling(true)
        val b, c = fresh[Int]
        q === cons(b,c) &&
        pathL("a",b,c)
      }
    }
    println("done")
  }

  test("pathRT") {
    expectResult(List(
      "pair(pair(b,1),cons(path(a,b,1),nil))",
      "pair(pair(c,2),cons(path(b,c,1),cons(path(a,c,2),nil)))",
      "pair(pair(a,3),cons(path(c,a,1),cons(path(b,a,2),cons(path(a,a,3),nil))))"
    )) {
      tabling(true)
      runN[(String,List[List[String]])](5) { case Pair(Pair(b,c),t) =>
        pathRT("a",b.asInstanceOf[Exp[String]],c.asInstanceOf[Exp[Int]]) && globalTrace() === t
      }
    }
    println("done")
  }

  test("pathLT") {
    expectResult(List(
      "pair(pair(b,1),cons(path(a,b,1),nil))",
      "pair(pair(c,2),cons(path(a,b,1),cons(path(a,c,2),nil)))",
      "pair(pair(a,3),cons(path(a,b,1),cons(path(a,c,2),cons(path(a,a,3),nil))))"
    )) {
      tabling(true)
      runN[(String,List[List[String]])](5) { case Pair(Pair(b,c),t) =>
        pathLT("a",b.asInstanceOf[Exp[String]],c.asInstanceOf[Exp[Int]]) && globalTrace() === t
      }
    }
    println("done")
  }
}
