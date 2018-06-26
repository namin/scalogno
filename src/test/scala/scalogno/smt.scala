package scalogno

import org.scalatest._

class TestSmt extends MySuite with Smt {
  test("1") {
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
  expectResult(List("1", "1", "2", "6", "24", "120", "720")) {
    runN[Int](7){ o => exists[Int]{n => faco(n,o)} }
  }
}
