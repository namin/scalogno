package scalogno
import scala.collection._

trait TablingBase extends Base with Engine {

  def memo(goal: Exp[Any])(a: => Rel): Rel

  def tabling(on: Boolean): Unit

  def dprintln(x: Any) = () // println(x)

}

trait TablingImpl extends TablingBase {
type Answer = (Exp[Any] => Unit)
case class Call(key: String, goal1: Exp[Any], cstore1: immutable.Set[Constraint], dvars1: immutable.Map[Int, Any], ldvars0: List[Exp[Any]], ldvars1: List[Exp[Any]], k1: Cont) {
  def load(ans: Answer): Unit = {
    // reset state to state at call
    cstore = cstore1; dvars = dvars1
    // equate actual state with symbolic before state
    dvarsEqu(ldvars0)
    // load constraints from answer
    ans(goal1);
    // update actual state to symbolic after state
    dvarsSet(ldvars1)
  }
}

  val ansTable = new mutable.HashMap[String, mutable.HashMap[String, Answer]]
  val contTable = new mutable.HashMap[String, List[Call]]

  var enabled = true

  def tabling(on: Boolean): Unit = {
    ansTable.clear
    contTable.clear
    enabled = on
  }

  // save complete call state
  def makeCall(goal0: Exp[Any], k: Cont): Call = {
    val dvarsRange = (0 until dvarCount).toList
    val ldvars0 = dvarsRange.map(i => fresh[Any]) // symbolic state before call
    val ldvars1 = dvarsRange.map(i => fresh[Any]) // symbolic state for continuation / after call

    // extend goal with symbolic state before and after
    val goal = term("goal",List(goal0, term("state0", ldvars0), term("state1", ldvars1)))

    // but disregard state for memoization (compute key for goal0)
    val key = extractStr(goal0)
    val cont = Call(key,goal,cstore,dvars,ldvars0,ldvars1,k)
    contTable(key) = cont::contTable.getOrElse(key,Nil)
    cont
  }

def makeAnswer(g1: Exp[Any]): Answer = {
  val lcstore = cstore
  val lidx = cstore groupBy { case IsTerm(id, _ , _) => id case _ => -1 }

  (g2: Exp[Any]) => {

    val stack = new mutable.BitSet(varCount)
    val seenVars = new mutable.HashMap[Int,Int]
    def copyVar(x: Exp[Any]): Exp[Any] = {
      val id = (Set(x.id) ++ (lcstore collect {
        case IsEqual(`x`,y) if y.id < x.id => y.id
        case IsEqual(y,`x`) if y.id < x.id => y.id
      })).min
      val mid = seenVars.getOrElseUpdate(id,seenVars.size)
      Exp(mid)
    }
    def copyTerm(x: Exp[Any]): Exp[Any] = lidx.getOrElse(x.id,Set.empty).headOption match {
      case Some(IsTerm(id, key, args)) =>
        assert(id == x.id)
        assert(!stack.contains(id), "cyclic terms not handled")
        try {
          stack += id
          term(key, args map copyTerm)
        } finally {
          stack -= id
        }
      case _ =>
        copyVar(x)
    }

    val g1_copy = copyTerm(g1)

    g1_copy === g2
  }
}

def dvarsSet(ls: List[Exp[Any]]) = {
  val dv = dvars
  dv foreach { case (k,v:Exp[Any]) => dvars += (k -> ls(k)) }
}
def dvarsEqu(ls: List[Exp[Any]]) =
  dvars foreach { case (k,v:Exp[Any]) => v === ls(k) }

def memo(goal0: Exp[Any])(a: => Rel): Rel = new Rel {
  override def exec(rec: Exec)(k: Cont): Unit = {
    if (!enabled) return rec(() => a)(k)

    def resume(cont: Call, ans: Answer) = rec{ () => cont.load(ans); Yes }(cont.k1)

    val cont = makeCall(goal0, k)
    ansTable.get(cont.key) match {
      case Some(answers) =>
        for (ans <- answers.values) resume(cont, ans)
      case None =>
        val ansMap = new mutable.HashMap[String, Answer]
        ansTable(cont.key) = ansMap
        rec { () =>
          dvarsSet(cont.ldvars0)
          a
        } { () =>
          dvarsEqu(cont.ldvars1)
          val ansKey = extractStr(goal0)
          ansMap.get(ansKey) match {
            case None =>
              val ans = makeAnswer(cont.goal1)
              ansMap(ansKey) = ans
              for (cont1 <- contTable(cont.key).reverse) {
                resume(cont1, ans)
              }
            case Some(_) =>
          }
        }
    }
  }
}
}
