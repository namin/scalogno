package scalogno

// TODO: in progress
// want to achieve something like
// https://github.com/namin/TAPL-in-miniKanren-cKanren-core.logic/blob/master/clojure-tapl/tapl/src/tapl/stlc_deriv.clj#L67
trait Deriv extends Base with ListBase {
  trait Goal
  type Clause = (Exp[Goal], Exp[List[Goal]]) => Rel
  def deriv(clause: Clause)(tree: Exp[List[List[Goal]]])(goals: Exp[List[Goal]]): Rel = {
    ((goals === nil) && (tree === nil)) ||
    exists[Goal,List[Goal],List[Goal],List[List[Goal]],List[List[Goal]]] { (g,gs,b,tb,ts) =>
      (goals === cons(g, gs)) &&
      clause(g,b) &&
      tree === cons(cons(g, tb), ts) &&
      deriv(clause)(tb)(b) &&
      deriv(clause)(ts)(gs)
    }
  }
}
