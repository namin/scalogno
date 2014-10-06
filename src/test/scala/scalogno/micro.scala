package scalogno

import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestMicroKanren extends FunSuite with MicroKanren {
  test("1") {
    expectResult(List(List(1, 2, 1))){
      run{exists{q =>
        conj(exists{x => exists{y => ===(q,List(x,y,x))}},
             exists{z => ===(q,List(1,2,z))})
      }}.toList
    }
  }

  test("2") {
    expectResult(List(List(1, 2, 1), List(2, 1, 2))){
      run{exists{q =>
        conj(exists{x => exists{y => ===(q,List(x,y,x))}},
             disj(exists{z => ===(q, List(1,2,z))},
                  exists{z => ===(q,List(2,1,z))}))}}.toList
    }
  }

  test("3") {
    expectResult(List(SVar(0))){run{exists{q => yes}}.toList}
  }


  def tree(as: Exp): Goal =
    disj(
      disj(        
        exists { z => conj(===(as,List(0,z)), tree(z)) },
          exists { z => conj(===(as,List(1,z)), tree(z)) }),
      ===(as,List()))
  
  test("interleaving") {
    val rs = run{exists{q => tree(q)}}.take(20).toList

    val str = rs.mkString("\n","\n","\n").replace("List","")
    val cmp = """
()
(0, ())
(1, ())
(0, (0, ()))
(1, (0, ()))
(0, (1, ()))
(1, (1, ()))
(0, (0, (0, ())))
(1, (0, (0, ())))
(0, (1, (0, ())))
(1, (1, (0, ())))
(0, (0, (1, ())))
(1, (0, (1, ())))
(0, (1, (1, ())))
(1, (1, (1, ())))
(0, (0, (0, (0, ()))))
(1, (0, (0, (0, ()))))
(0, (1, (0, (0, ()))))
(1, (1, (0, (0, ()))))
(0, (0, (1, (0, ()))))
"""
    // compare interleaving to BFS order:
    // BFS would yield
    // 0
    // 1
    // 0 0
    // 0 1
    // 1 0
    // 1 1
    // ...

    expectResult(cmp)(str)
  }


  def lookup(env: Exp, x: Exp, t: Exp): Goal =
    disj(exists { tail => (===(env,List("cons", x,t, tail))) },
         exists { x1 => exists { t1 => exists { tail => 
            conj(===(env,List("cons", x1,t1, tail)),
                 lookup(tail,x,1)) }}})

  def typed(n: Int, env: Exp, exp: Exp, typ: Exp): Goal = if (n == 0) no else
    disj(
      exists { x => 
        conj(===(exp,List("var",x)), lookup(env,x,typ)) },
    disj(
      exists { x => exists { y => exists { t1 => exists { t2 => 
        conj(===(exp,List("lam",x,y)), conj(===(typ,List("arrow",t1,t2)), 
            typed(n-1,List("cons",x,t1,env),y,t2))) }}}},
    disj(
      exists { x => exists { y => exists { t1 => exists { t2 => 
        conj(===(exp,List("app",x,y)), conj(===(typ,t2), 
          conj(typed(n-1,env,x,List("arrow",t1,t2)), 
               typed(n-1,env,y,t1)))) }}}},
    disj(
      exists { x => exists { t2 => 
        conj(===(exp,List("fst",x)), typed(n-1,env,x,List("times",typ,t2))) }},
    disj(
      exists { x => exists { t1 => 
        conj(===(exp,List("snd",x)), typed(n-1,env,x,List("times",t1,typ))) }},
    disj(
      exists { x1 => exists { t1 => exists { x2 => exists { t2 => 
        conj(===(exp,List("pair",x1,x2)), conj(===(typ,List("times",t1,t2)), 
          conj(typed(n-1,env,x1,t1),
               typed(n-1,env,x2,t2)))) }}}},
    no))))))


  test("typed1") {
    expectResult(List("var", "x")) {
      run{exists{q => typed(5,List("cons", "x", "foo", "nil"),q,"foo")}}.head
    }
  }

  test("typed2") {
    expectResult(List("fst", List("var", "x"))) {
      run{exists{q => typed(5,List("cons", "x", List("times", "A", "B"), "nil"),q,"A")}}.head
    }
  }

  test("typed3") {
    expectResult(List("pair", List("snd", List("var", "x")), List("fst", List("var", "x")))) {
      run{exists{q => typed(5,List("cons", "x", List("times", "A", "B"), "nil"),q,List("times", "B", "A"))}}.head
    }
  }

  test("typed4") {
    // A & B => B & A
    expectResult("List(lam, _.0, List(pair, List(snd, List(var, _.0)), List(fst, List(var, _.0))))") {
      run{exists{q => typed(5,"nil",q,List("arrow", List("times", "A", "B"), List("times", "B", "A")))}}.head.toString
    }
  }

  test("typed5") {
    // A & (A => B) => B
    expectResult("List(lam, _.0, List(app, List(snd, List(var, _.0)), List(fst, List(var, _.0))))") {
      def infix_&(a:Any,b:Any) = List("times",a,b)
      def infix_->(a:Any,b:Any) = List("arrow",a,b)
      run{exists{q => typed(5,"nil",q, ("A" & ("A" -> "B")) -> "B")}}.head.toString
    }
  }

}
