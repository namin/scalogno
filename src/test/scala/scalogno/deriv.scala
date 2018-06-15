package scalogno

class TestDeriv extends MySuite with Deriv with MetaSTLC with STLC_ReverseDeBruijn with Prettify
{
  val g = new Graph[String] {
    def edge(x:Exp[String],y:Exp[String]) =
      (x === "a") && (y === "b") ||
      (x === "b") && (y === "c") ||
      (x === "c") && (y === "a")
  }

  test("deriv") {
    expectResult(List(
      "(path(a,b) <-- ())",
      "(path(a,c) <-- ((path(b,c) <-- ())))",
      "(path(a,a) <-- ((path(b,a) <-- ((path(c,a) <-- ())))))",
      "(path(a,b) <-- ((path(b,b) <-- ((path(c,b) <-- ((path(a,b) <-- ())))))))",
      "(path(a,c) <-- ((path(b,c) <-- ((path(c,c) <-- ((path(a,c) <-- ((path(b,c) <-- ())))))))))"
    )) {
      prettify(runN[List[List[Goal]]](5) { q =>
        exists[List[Any]] { p =>
          deriv(pathClause1(g))(q)(cons(pathTerm("a",p),nil))
        }
      })
    }
  }

  test("deriv_stlc") {
    expectResult(List(
      "(tc(|-(nil,lam(z,lam(s(z),@(var(z),var(s(z))))),->(->(x0,x1),->(x0,x1)))) <-- ((tc(|-(cons(->(x0,x1),nil),lam(s(z),@(var(z),var(s(z)))),->(x0,x1))) <-- ((tc(|-(cons(x0,cons(->(x0,x1),nil)),@(var(z),var(s(z))),x1)) <-- ((tc(|-(cons(x0,cons(->(x0,x1),nil)),var(z),->(x0,x1))) <-- ()) (tc(|-(cons(x0,cons(->(x0,x1),nil)),var(s(z)),x0)) <-- ())))))))"
    )) {
      prettify(runN[List[List[Goal]]](3) { q =>
        val x,y = fresh[Sym]
        val a = nil |- lam(x, lam(y, (sym(x) app sym(y)))) :: fresh[LType]
        exists[List[Goal]] { goals =>
          reifyGoals(typecheck(a))(goals) &&
          deriv(allclausesRel)(q)(goals)
        }
      })
    }
  }
}
