import mk._ // TODO: not extensible?

trait InjectBase {
  trait Inject[T] {
    def toTerm(x: T): Term[T]
  }

  implicit def inject[T:Inject](x: T) = implicitly[Inject[T]].toTerm(x)

  implicit val injectString = new Inject[String] {
    def toTerm(s: String): Term[String] = Atom(s)
  }
}

trait Ordering {
  trait Ord[T] {
    def lt(x: Term[T], y: Term[T]): Goal
  }

  implicit class OrdOps[T:Ord](x: Term[T]) {
    def <(y: Term[T]): Goal = implicitly[Ord[T]].lt(x, y)
  }
}

trait NatBase extends Ordering {
  type Nat

  implicit val ordNat = new Ord[Nat] {
    def lt(x: Term[Nat], y: Term[Nat]): Goal = lessThan(x, y)
  }

  def nat(x: Int): Term[Nat] = if (x == 0) zero else succ(nat(x-1))

  def succ(n: Term[Nat]): Term[Nat] = Fun("s", List(n))
  def zero: Term[Nat] = Atom("z")

  def lessThan(a: Term[Nat], b: Term[Nat]): Goal = rel{
    fresh[Nat]{b1 => b === succ(b1) &&
      (a === zero ||
        fresh[Nat]{a1 => a === succ(a1) &&
          lessThan(a1, b1)
      })
    }
  }

  def plus(a: Term[Nat], b: Term[Nat], c: Term[Nat]): Goal = rel{
    (a === zero && b === c) ||
    freshN[Nat](2) { case List(a1,c1) =>
      a === succ(a1) && c === succ(c1) && plus(a1,b,c1)
    }
  }
}

object scalogno extends InjectBase with Ordering with NatBase

object scalogno_tests extends App {
  import scalogno._

  assert(runA[Nat]{q => lessThan(nat(3), q)} == List(succ(succ(succ(succ(Atom[Nat]("_0")))))))

}
