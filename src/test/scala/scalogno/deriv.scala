package scalogno

class TestDeriv extends MySuite with Deriv with Prettify
//with STLC with STLC_ReverseDeBruijn with STLC_Nat
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
}
