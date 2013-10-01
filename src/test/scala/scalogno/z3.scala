package scalogno

import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

import z3.scala._
import z3.scala.dsl._

@RunWith(classOf[JUnitRunner])
class TestZ3 extends FunSuite {
  def isPrime(i : Int) : Boolean = {
    ! (2 to i-1).exists(i % _ == 0)
  }

  test("paper ex: implicit computation using Z3") {
    expectResult(Set((1,2,12), (3,5,25), (3,11,121), (3,7,49), (1,5,75), (1,3,27), (1,7,147), (1,11,363))) {
      (for(
        (x,y) <- findAll((x: Val[Int], y: Val[Int]) => x > 0 && y > x && x * 2 + y * 3 <= 40);
        if(isPrime(y));
        z <- findAll((z: Val[Int]) => z * x === 3 * y * y))
       yield (x, y, z)).toSet
    }
  }
}
