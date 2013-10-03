package scalogno

import scala.language.implicitConversions

trait MicroLf1ExNaturals extends MicroLf1 {
  val nat    = typ                                     -- "nat"
  val z      = nat                                     -- "z"
  val s      = nat *=>: nat                            -- "s"

  val plus   = nat *=>: nat *=>: nat *=>: typ          -- "plus"
  val plus_z = nat { n => plus(z)(n)(n) }              -- "plus_z"
  val plus_s = nat { n1 => nat { n2 => nat { n3 =>
    plus(n1)(n2)(n3) *=>:
    plus(s(n1))(s(n2))(s(n3))
  }}}                                                  -- "plus_s"
}

trait MicroLf1 {
  /// e := (c_n e_i|_{i=0..n-1})
  /// t_n := ((x_i: e_i) ->)|_{i=0..n-1} e_n
  /// d := c_n : t_n

  trait T
  trait A extends T
  trait F[X <: T] extends T

  case class SyntaxApp[X <: T, Y <: T](s: Sym[X], args: App[Y]) {
    def apply(e: Const) = SyntaxApp[X, F[Y]](s, AppFor(e, args))
  }
  implicit def symToTyp(s: Sym[A]): Typ[A] = TypAtom(symToConst(s))
  implicit def symToConst(s: Sym[A]): Const = ConstApp(s, AppAtom)
  implicit def symToApp[X <: T](s: Sym[F[X]]): SyntaxApp[F[X],A] = SyntaxApp(s, AppAtom)
  implicit def closeAppConst[X <: T](app: SyntaxApp[X,X]): Const = ConstApp(app.s, app.args)
  implicit def closeAppTyp[X <: T](app: SyntaxApp[X,X]): Typ[A] = TypAtom(closeAppConst(app))
  def typ: Sym[A] = Sym("type")

  sealed abstract class Typ[X <: T] {
    def --(id: String): Sym[X] = {
      Sym[X](id)
    }
    def *=>:(e: Const) = TypFor(e, x => this)
  }
  case class TypAtom(e: Const) extends Typ[A]
  case class TypFor[X <: T](e: Const, f: Const => Typ[X]) extends Typ[F[X]]

  case class Sym[X <: T](id: String)

  sealed abstract class Const {
    def apply[X <: T](f: Const => Typ[X]) = TypFor(this, f)
  }
  case class ConstApp[X <: T](s: Sym[X], args: App[X]) extends Const

  sealed abstract class App[X <: T]
  case object AppAtom extends App[A]
  case class AppFor[X <: T](e1: Const, es: App[X]) extends App[F[X]]

}
