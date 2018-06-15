package scalogno

trait MetaBase extends ListBase with Engine {
  trait Goal
  type Clause = (Exp[Goal], Exp[List[Goal]]) => Rel

  def existsC[T,U](f: (Exp[T],Exp[U]) => Clause): Clause = {
    f(fresh[T],fresh[U])
  }
}

/*
(define (vanilla* clause)
  (define (solve* goals)
    (conde
      ((== goals ’()))
      ((fresh (g gs body)
        (== (cons g gs) goals)
        (clause g body)
        (solve* body)
        (solve* gs)))))
  solve*)
*/
trait MetaVanilla extends MetaBase {
  def vanilla(clause: Clause)(goals: Exp[List[Goal]]): Rel =
    goals === nil ||
    exists[Goal,List[Goal],List[Goal]] { (g, gs, body) =>
      (goals === cons(g,gs)) &&
      clause(g,body) &&
      vanilla(clause)(body) &&
      vanilla(clause)(gs)
    }
}

/*
(define (tracer* clause)
  (define (solve* goals trace-in trace-out)
    (conde
      ((== goals '())
       (== trace-in trace-out))
      ((fresh (g gs body trace-out-body)
         (== (cons g gs) goals)
         (clause g body)
         (solve* body (cons g trace-in) trace-out-body)
         (solve* gs trace-out-body trace-out)))))
  (lambda (goal t)
    (solve* (list goal) '() t)))
*/
trait MetaTracer extends MetaBase {
  def tracer(clause: Clause)(in: Exp[List[Goal]], out: Exp[List[Goal]])(goals: Exp[List[Goal]]): Rel =
    ((goals === nil) && (in === out)) ||
    exists[Goal,List[Goal],List[Goal],List[Goal]] { (g, gs, body, out_body) =>
      (goals === cons(g,gs)) &&
      clause(g,body) &&
      tracer(clause)(cons(g,in),out_body)(body) &&
      tracer(clause)(out_body,out)(gs)
    }


}

trait MetaReify extends MetaBase {
  // auto reification !!!

  var allclauses = Map[String,Clause]()
  val moregoals: DVar[Exp[List[Goal]]] = DVar(fresh)

  def rule[A,B](s: String)(f:(Exp[A], Exp[B]) => Rel) = {
    def goalTerm(a: Exp[A], b: Exp[B]) = term[Goal](s,List(a,b))

    allclauses += s ->
      { (head: Exp[Goal], body: Exp[List[Goal]]) =>
        exists[A,B] { (a,b) =>
          (head === goalTerm(a,b)) && reifyGoals(f(a,b))(body)
        }
      }

    {(a: Exp[A], b: Exp[B]) =>
      val hole = moregoals()
      moregoals := fresh
      hole === cons(goalTerm(a,b),moregoals())
    }
  }

  def reifyGoals(goal: => Rel)(goals: Exp[List[Goal]]): Rel = {
    moregoals := goals
    goal && moregoals() === nil
  }

    def reifyClause(goal: => Rel)(head: Exp[Goal], body: Exp[List[Goal]]): Rel = {
    reifyGoals(goal)(cons(head,nil)) && {
      val s = extractStr(head)
      val key = s.substring(0,s.indexOf("(")) // a bit hacky, but hey ...
      println(key)
      allclauses(key)(head,body)
    }
  }

  def allclausesRel: Clause = { (head: Exp[Goal], body: Exp[List[Goal]]) =>
    ((No:Rel) /: allclauses.values) ((r,c) => r || c(head,body))
  }
}

trait MetaReifyVanilla extends MetaReify {
  def vanilla2(goal: => Rel): Rel =
    exists[List[Goal]] { goals =>
      reifyGoals(goal)(goals) && vanilla2(goals)
    }

  def vanilla2(goals: Exp[List[Goal]]): Rel = {
    goals === nil ||
    exists[Goal,List[Goal],List[Goal]] { (g, gs, body) =>
      (goals === cons(g,gs)) &&
      allclausesRel(g,body) &&
      vanilla2(body) &&
      vanilla2(gs)
    }
  }
}
