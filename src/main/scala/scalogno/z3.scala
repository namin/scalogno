package scalogno

import z3.scala._
import z3.scala.dsl._

trait Z3Base extends Base {
  def sat[T:ValHandler](e: Exp[Any])(predicate: Val[T] => Tree[BoolSort]): Rel = {
    findAll(predicate).foldLeft(No:Rel){(r,v) => Or(() => r, () => {register(IsTerm(e.id, v.toString, Nil)); Yes})}
  }
}
