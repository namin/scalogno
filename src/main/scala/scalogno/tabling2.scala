package scalogno.old

import scalogno._

trait TablingPaper extends TablingBase {
import scala.collection._
case class Call(key: String)
case class Answer(key: String)
def key(name: String, args: Exp[Any]*): String =
  name+"("+args.map(extractStr).mkString(",")+")"
def makeCall(name: String, args: Exp[Any]*): Call =
  Call(key(name, args: _*))
def makeAnswer(name: String, args: Exp[Any]*): Answer =
  Answer(key(name, args: _*))
val callTable = new mutable.HashMap[String, (mutable.HashSet[Call], mutable.HashSet[Answer])]
// tabling combinator
def memo[A,B](name: String)(f: (Exp[A], Exp[B]) => Rel)(a: Exp[A], b: Exp[B]): Rel = new Rel {
  override def exec(call: Exec)(k: Cont): Unit = {
    def resume(cont: Call, ans: Answer) = ???
    val cont = makeCall(name, a, b)
    callTable.get(cont.key) match {
      case Some((conts, answers)) =>                         // call key found:
        conts += cont                                        //   save continuation for later
        for (ans <- answers.toList) resume(cont, ans)        //   continue with stored answers
      case None =>                                           // call key not found:
        val answers = new mutable.HashSet[Answer]            //   add table entry
        val conts   = new mutable.HashSet[Call]  
        callTable(cont.key) = (conts,answers)  
        conts += cont                                        //   store continuation
        call { () => f(a,b) } { () =>                        //   execute rule body
          val ans = makeAnswer(name, a, b)
          if (!answers.contains(ans)) {                      
            answers += ans                                   //   record each new answer and
            for (cont1 <- conts.toList) resume(cont1, ans)   //   resume stored continuations
} } }   } }
}

trait Tabling1 extends TablingBase {

  type Entry = Exp[Any]

  var table = new scala.collection.mutable.HashMap[String, Entry]

  var enabled = true

  def tabling(on: Boolean): Unit = {
    table.clear
    enabled = on
  }

  def memo(goal: Exp[Any])(a: => Rel): Rel = new Rel {
    override def exec(rec: Exec)(k: Cont): Unit = {
      val key = extractStr(goal)
      table.get(key) match {
        case Some(goal1) if enabled =>
          dprintln(key + " seen: " + extractStr(goal1))
          goal === goal1 // FIXME: not general enough!!!
          // TODO: invoke continuation with all stored answers
          // store continuation so that it can be called for future answers
          k()
        case _ =>
          println(key)
          table(key) = goal
          rec(() => a) { () =>
            if (enabled) dprintln("answer for "+key+": " + extractStr(goal))
            // TODO: memoize answer (if exists ignore?)
            // invoke all stored continuations with new answer
            k()
          }
      }
    }
  }

}


trait Tabling2 extends TablingBase {

  type Answer = (Exp[Any] => Unit)
  type Call = (Exp[Any], Set[Constraint], Map[Int, Any], List[Exp[Any]], List[Exp[Any]], Cont)

  val ansTable = new scala.collection.mutable.HashMap[String, scala.collection.mutable.HashMap[String, Answer]]
  val contTable = new scala.collection.mutable.HashMap[String, List[Call]]

  var enabled = true

  def tabling(on: Boolean): Unit = {
    ansTable.clear
    contTable.clear
    enabled = on
  }


  def constrainAs(g1: Exp[Any]): Answer = { // TODO!
    val lcstore = cstore
    val lidx = cstore groupBy { case IsTerm(id, _ , _) => id case _ => -1 }

    val k1 = extractStr(g1)
    (g2: Exp[Any]) => {

      val stack = new scala.collection.mutable.BitSet(varCount)
      val seenVars= new scala.collection.mutable.HashMap[Int,Int]
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

      val g1x = copyTerm(g1)
      val k1x = extractStr(g1x)
      //assert(k1x == k1, s"expect $k1 but got $k1x") disabled for dvar init: default might not be written yet
      val k2 = extractStr(g2)
      dprintln(s"$k2 --> $k1")

      g1x === g2
    }
  }

  def memo(goal0: Exp[Any])(a: => Rel): Rel = new Rel {
    override def exec(rec: Exec)(k: Cont): Unit = {
      if (!enabled) return rec(() => a)(k)

      val dvarsRange = (0 until dvarCount).toList
      def dvarsSet(ls: List[Exp[Any]]) = { val dv = dvars; dv foreach { case (k,v:Exp[Any]) => dvars += (k -> ls(k)) } }
      def dvarsEqu(ls: List[Exp[Any]]) = dvars foreach { case (k,v:Exp[Any]) => v === ls(k) }

      def invoke(cont: Call, a: Answer) = {
        val (goal1, cstore1, dvars1, ldvars0, ldvars1, k1) = cont
        rec{ () =>
          // reset state to state at call
          cstore = cstore1; dvars = dvars1
          // equate actual state with symbolic before state
          dvarsEqu(ldvars0)
          // load constraints from answer
          a(goal1);
          // update actual state to symbolic after state
          dvarsSet(ldvars1)
          Yes
        }(k1)
      }

      val ldvars0 = dvarsRange.map(i => fresh[Any]) // symbolic state before call
      val ldvars1 = dvarsRange.map(i => fresh[Any]) // symbolic state for continuation / after call

      // extend goal with symbolic state before and after
      val goal = term("goal",List(goal0, term("state0", ldvars0), term("state1", ldvars1)))

      // but disregard state for memoization (compute key for goal0)
      val key = extractStr(goal0)

      val cont: Call = (goal,cstore,dvars,ldvars0,ldvars1,k) // save complete call state
      contTable(key) = cont::contTable.getOrElse(key,Nil)
      ansTable.get(key) match {
        case Some(answers) =>
          //dprintln("found " + key)
          for ((ansKey, ansConstr) <- answers.toList) // mutable! convert to list
            invoke(cont,ansConstr)
        case _ =>
          dprintln(key)
          val ansMap = new scala.collection.mutable.HashMap[String, Answer]
          ansTable(key) = ansMap
          rec { () =>
            // evaluate goal with symbolic before state, to obtain rep of state after
            dvarsSet(ldvars0)
            a
          } { () =>
            // constraint symbolic after state
            dvarsEqu(ldvars1)
            // disregard state again for memoization
            val ansKey = extractStr(goal0)
            ansMap.get(ansKey) match {
              case None =>
                dprintln("answer for "+key+": " + ansKey)
                val ansConstr = constrainAs(goal)
                ansMap(ansKey) = ansConstr
                var i = 0
                for (cont1 <- contTable(key).reverse) {
                  //println("call cont "+i+" with "+key+" -> "+ansKey); i+=1
                  invoke(cont1,ansConstr)
                }
              case Some(_) => // fail
                //println("answer for "+key+": " + ansKey + " (duplicate)")
            }
          }
      }
    }
  }
}
