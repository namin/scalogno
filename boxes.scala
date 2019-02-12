object boxes extends App {
  val solver = new SmtSolver()
  solver.init()
  abstract class R
  case class I(v: Int) extends R {
    override def toString = v.toString
  }
  case class V(id: Int) extends R {
    override def toString = s"x$id"
  }
  case class Box(x: R, y: R, w: R, h: R)
  var vars: Map[Int,Int] = Map.empty
  def addAssert(s: String) = {
    solver.add(s"(assert $s)")
  }
  def set(a: R, b: R) = {
    addAssert(s"(= $a $b)")
  }
  def basic(b: Box) = {
    addAssert(s"(>= ${b.x} 0)")
    addAssert(s"(>= ${b.y} 0)")
    addAssert(s"(>= ${b.w} 1)")
    addAssert(s"(>= ${b.h} 1)")
  }
  def contains(b: Box, a: Box) = {
    addAssert(s"(> ${a.x} ${b.x})")
    addAssert(s"(> ${a.y} ${b.y})")
    addAssert(s"(< (+ ${a.x} ${a.w}) (+ ${b.x} ${b.w}))")
    addAssert(s"(< (+ ${a.y} ${a.h}) (+ ${b.y} ${b.h}))")
  }
  var count = -1
  def fresh() = {
    count += 1
    solver.decl(count)
    V(count)
  }
  def box() = {
    val b = Box(fresh(), fresh(), fresh(), fresh())
    basic(b)
    b
  }
  def example() = {
    var p: Box = null
    for (i <- (0 until 10)) {
      val b = box()
      if (p != null) {
        contains(p, b)
      }
      p = b
    }
    solver.checkSat()
    solver.extractModel({(x,v) => vars += (x -> v)})
    solver.smt.close()
  }
  example()
}
