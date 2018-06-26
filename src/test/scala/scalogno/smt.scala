package scalogno

import org.scalatest._

class TestExe extends MySuite with Smt {
  test("1") {
    smt_init()
    smt.write("(assert (= 1 0))")
    smt.write("(check-sat)")
    expectResult("unsat") { smt.readAtom() }
    smt.close()
  }
}

class TestSmt extends MySuite with Smt {
  ignore("1") {
    expectResult(List("1")) {
      run[Int] { q =>
        q ==? 1
      }
    }
  }
}

class TestFactorial extends MySuite with Smt {
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

class TestFib extends MySuite with Smt /*with ListBase with TablingBase with TablingImpl*/ {
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
