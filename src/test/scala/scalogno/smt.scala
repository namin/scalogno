package scalogno

import org.scalatest._

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
    (
      (n ==? 0) && (o ==? 1) ||

      exists[Int,Int]{(n1,r) =>
        (n - 1) ==? n1 &&
          (n * r) ==? o &&
        faco(n1, r)
      }
    )

  ignore("7") {
    expectResult(List("1", "1", "2", "6", "24", "120", "720")) {
      runN[Int](7){ o => exists[Int]{n => faco(n,o)} }
    }
  }
}

class TestFib extends MySuite with Smt with Engine/*with ListBase with TablingBase with TablingImpl*/ {
  def fibo(n: Exp[Int], o: Exp[Int]): Rel = /*memo(term("fibo", List(n,o)))*/ {
    ((n ==? 0) && (o ==? 1)) ||
    ((n ==? 1) && (o ==? 2)) ||
    { val n1,n2,o1,o2 = fresh[Int]
      (n > 0) &&
      (n1 ==? (n - 1)) &&
      (n2 ==? (n - 2)) &&
      (o ==? o1 + o2) &&
      fibo(n2, o2) &&
      fibo(n1, o1) }

  }

  ignore("6") {
    expectResult(List("1", "2", "3", "5", "8", "13")) {
      runN[Int](6){ o => exists[Int]{n => fibo(n,o)} }
    }
  }
}
