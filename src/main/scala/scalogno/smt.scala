package scalogno

trait Smt extends Base {
  trait Z[+T]
  case class A[+T](x: Exp[T]) extends Z[T] {
    override def toString = {
      cstore.collect{ case(IsTerm(id, k, _)) if x.id == id => k}.toList.head
    }
  }
  case class P[+T](s: String, args: List[Z[Any]]) extends Z[T] {
    override def toString = {
      val a = args.mkString(" ")
      s"($s$a)"
    }
  }
  val zs = DVar[List[P[Any]]](Nil)

  def zAssert(p: P[Boolean]): Rel = new Rel {
    def exec(call: Exec)(k: Cont): Unit = {} // TODO
  }
  implicit def toZInt(e: Exp[Int]): Z[Int] = A(e)
  implicit class ZIntOps(a: Z[Int]) {
    def ===(b: Z[Int]): Rel = zAssert(P("=", List(a, b)))
    def >(b: Z[Int]): Rel = zAssert(P(">", List(a, b)))
    def -(b: Z[Int]): Z[Int] = P("-", List(a, b))
    def *(b: Z[Int]): Z[Int] = P("*", List(a, b))
  }

}
