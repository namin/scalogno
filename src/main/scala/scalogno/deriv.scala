package scalogno

// TODO: in progress
// want to achieve something like
// https://github.com/namin/TAPL-in-miniKanren-cKanren-core.logic/blob/master/clojure-tapl/tapl/src/tapl/stlc_deriv.clj#L67
trait Deriv extends MetaGraphBase {
  def deriv(clause: Clause)(tree: Exp[List[List[Goal]]])(goals: Exp[List[Goal]]): Rel = {
    ((goals === nil) && (tree === nil)) ||
    exists[Goal,List[Goal],List[Goal],List[List[Goal]],List[List[Goal]]] { (g,gs,b,tb,ts) =>
      (goals === cons(g, gs)) &&
      clause(g,b) &&
      tree === cons(cons(g, cons("<--", cons(tb, nil))), ts) &&
      deriv(clause)(tb)(b) &&
      deriv(clause)(ts)(gs)
    }
  }
}

trait MetaSTLC extends STLC with MetaGraphBase {
  def tc(d: Exp[Deriv]): Rel = exists[String] { c => tcd(c, d) }
  def tcd: (Exp[String], Exp[Deriv]) => Rel =
    rule("tc") { (c,d) =>
    (c === "var" && exists[Env,Sym,LType] { (G,x,t1) =>
      val a = G |- sym(x) :: t1

      d === a && lookup(G,x,t1)
    }) ||
    (c === "lam" && exists[Env,Env,Sym,LTerm,LType,LType] { (G,G1,x,e,t1,t2) =>
      val a = G |- lam(x,e) :: (t1 -> t2)
      val b = G1 |- e :: t2

      d === a && extend(G,x,t1,G1) && tc(b)
    }) ||
    (c === "app" && exists[Env,LTerm,LTerm,LType,LType] { (G,e1,e2,t1,t2) =>
      val a = G |- (e1 app e2) :: t2
      val b = G |- e1 :: (t1 -> t2)
      val c = G |- e2 :: t1

      d === a && tc(b) && tc(c)
    })
    }
}
