package scalogno

import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestNaturals extends FunSuite with Base with Engine with Naturals with ListBase {
  test("3 first nats") {
    expectResult(List("z", "s(z)", "s(s(z))")) {
      run[LF](Some(3)) {
        case Term(q) =>
          searchNat(q.typed(nat))
      }
    }
  }
}

