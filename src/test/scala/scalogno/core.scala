package scalogno

import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestCore extends FunSuite with Core {
  test("1") {
    expectResult(List(List(1, 2, 1))){
      run{q =>
        E{x => E{y => q*=*List(x,y,x)}} *&*
        E{z => q*=*List(1,2,z)}
      }
    }
  }

  test("2") {
    expectResult(List(List(1, 2, 1), List(2, 1, 2))){
      run{q =>
        E{x => E{y => q*=*List(x,y,x)}} *&*
        (E{z => q*=*List(1,2,z)} *|*
         E{z => q*=*List(2,1,z)})
      }
    }
  }

  test("3") {
    expectResult(List(SVar(0))){run{q => yes}}
  }
}
