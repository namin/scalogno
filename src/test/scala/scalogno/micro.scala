package scalogno

import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestMicroKanren extends FunSuite with MicroKanren {
  test("1") {
    expectResult(List(List(1, 2, 1))){
      run{exists{q =>
        conj(exists{x => exists{y => ===(q,List(x,y,x))}},
             exists{z => ===(q,List(1,2,z))})
      }}.toList
    }
  }

  test("2") {
    expectResult(List(List(1, 2, 1), List(2, 1, 2))){
      run{exists{q =>
        conj(exists{x => exists{y => ===(q,List(x,y,x))}},
             disj(exists{z => ===(q, List(1,2,z))},
                  exists{z => ===(q,List(2,1,z))}))}}.toList
    }
  }

  test("3") {
    expectResult(List(SVar(0))){run{exists{q => yes}}.toList}
  }
}
