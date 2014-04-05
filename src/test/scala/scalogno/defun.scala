package scalogno

import scala.language.implicitConversions

import org.scalatest._

class TestDefun extends FunSuite with ListBase with NatBase with Engine {

  test("defun0") {
    expectResult(11) {
      val f = new Gen0
      f(4)
    }
  }

  test("defun1") {
    expectResult(List(
      "s(s(s(s(s(s(s(s(s(s(s(z)))))))))))"
    )) {
      runN[Int](5) { q =>
        val f = new Gen1
        f.runv(4,q)
      }
    }
  }

  test("defun2") {
    expectResult(List(
      "pair(z,s(z))", 
      "pair(s(z),s(s(z)))", 
      "pair(s(s(z)),s(s(s(s(z)))))", 
      "pair(s(s(s(z))),s(s(s(s(s(s(s(z))))))))", 
      "pair(s(s(s(s(z)))),s(s(s(s(s(s(s(s(s(s(s(z))))))))))))"
    )) {
      runN[(Int,Int)](5) { case Pair(q1,q2) =>
        val f = new Gen1
        f.runv(q1,q2)
      }
    }
  }

  test("defun3") {
    expectResult(List(
      "pair(pair(fapp3(x0,x1,x2,x3,z,XXtop),s(s(s(s(z))))),pair(fif2(x0,x1,x2,x3,z,XXtop),s(s(s(s(z))))))", 
      "pair(pair(fapp3(x0,x1,x2,x3,s(z),XXtop),s(s(s(z)))),pair(fif2(x0,x1,x2,x3,s(z),XXtop),s(s(s(s(z))))))"
    )) {
      runN[(Any,Any)](2) { case Pair(q1,q2) =>
        val f = new Gen1
        // explore states backwards
        f.step(q2,pair(f.XXtop(),4)) && f.step(q1,q2)
      }
    }
  }

// cps converted, defunctionalized factorial function
// (generated code from github/tiarkrompf/interpreters)

class Gen0 extends (Int => Int) {
type V = Int
type R = Unit
type K = V => R
type F = ((V,K)) => R
type KF = F => R

def clos(f:F) = f
def fclos(f:((F,KF))=>R): F = XXfix(f)

val log = false

abstract class Fun[T] extends (T=>Unit) with Product { 
override def toString = productPrefix + '(' + productIterator.mkString(",") + ')'
def apply(x:T) = { if (log) println("call "+this+" -- "+x); call(this,x) }}
case class main0() extends Fun[(V,K)]
case class ffix1(ymain:V,kmain:K) extends Fun[(F,KF)]
case class flam2(ymain:V,kmain:K,yfix:F,kfix:KF) extends Fun[(V,K)]
case class fthen3(ymain:V,kmain:K,yfix:F,kfix:KF,ylam:V,klam:K) extends Fun[(Unit)]
case class fapp3(ymain:V,kmain:K,yfix:F,kfix:KF,ylam:V,klam:K) extends Fun[V]
case class felse3(ymain:V,kmain:K,yfix:F,kfix:KF,ylam:V,klam:K) extends Fun[(Unit)]
case class fif2(ymain:V,kmain:K,yfix:F,kfix:KF,ylam:V,klam:K) extends Fun[V]
case class fapp0(ymain:V,kmain:K) extends Fun[V]
case class XXfix(f:((F,KF))=>R) extends Fun[(V,K)]
case class XXpart(x:V,k:K) extends Fun[F]
case class XXtop() extends Fun[V]
def call[T](f: Fun[T], x: T): Unit = (f,x) match {
  case (fthen3(ymain:V,kmain:K,yfix:F,kfix:KF,ylam:V,klam:K), ()) =>
    val xp = ylam + -1
    yfix(xp,fapp3(ymain,kmain,yfix,kfix,ylam,klam))
  case (fapp3(ymain:V,kmain:K,yfix:F,kfix:KF,ylam:V,klam:K), yapp: V) =>
    val xt = ylam + yapp // use add instead of mult
    fif2(ymain,kmain,yfix,kfix,ylam,klam)(xt)
  case (felse3(ymain:V,kmain:K,yfix:F,kfix:KF,ylam:V,klam:K), ()) =>
    fif2(ymain,kmain,yfix,kfix,ylam,klam)(1)
  case (flam2(ymain:V,kmain:K,yfix:F,kfix:KF), (ylam:V,klam:K)) =>
    if (ylam != 0) fthen3(ymain,kmain,yfix,kfix,ylam,klam)() else felse3(ymain,kmain,yfix,kfix,ylam,klam)()
  case (fif2(ymain:V,kmain:K,yfix:F,kfix:KF,ylam:V,klam:K), yif: V) =>
    klam(yif)
  case (ffix1(ymain:V,kmain:K), (yfix:F,kfix:KF)) =>
    kfix(clos(flam2(ymain,kmain,yfix,kfix)))
  case (main0(), (ymain:V,kmain:K)) =>
    fclos(ffix1(ymain,kmain))(ymain,fapp0(ymain,kmain))
  case (fapp0(ymain:V,kmain:K), yapp: V) =>
    kmain(yapp)
  case (f1@XXfix(f:(((F,KF))=>R)), (x:V,k:K)) =>
    //f((f1, f2 => f2(x,k)))
    f((f1,XXpart(x,k)))
  case (XXpart(x,k), (f:F)) =>
    f(x,k)
  case (XXtop(), y:V) =>
    exit(y)
}
var exit: K = null
def apply(x: Int): Int = {
  exit = { (y:Int) => return y }

  main0()(x,XXtop()); -1
}
}


// relational version

class Gen1 {
type V0 = Int
type V = Exp[V0]
type R0 = Unit
type R = Rel
type K0 = V0 => R0
type K = Exp[K0]
type F0 = ((V0,K0)) => R0
type F = Exp[F0]
type KF0 = F0 => R0
type KF = Exp[KF0]

type Fun[T] = Exp[T => Unit]

def main0(): Fun[(V0,K0)]                                             = term("main0",List())
def ffix1(ymain:V,kmain:K): Fun[(F0,KF0)]                             = term("ffix1",List(ymain:V,kmain:K))
def flam2(ymain:V,kmain:K,yfix:F,kfix:KF): Fun[(V0,K0)]               = term("flam2",List(ymain:V,kmain:K,yfix:F,kfix:KF))
def fthen3(ymain:V,kmain:K,yfix:F,kfix:KF,ylam:V,klam:K): Fun[(Unit)] = term("fthen3",List(ymain:V,kmain:K,yfix:F,kfix:KF,ylam:V,klam:K))
def fapp3(ymain:V,kmain:K,yfix:F,kfix:KF,ylam:V,klam:K): Fun[V0]      = term("fapp3",List(ymain:V,kmain:K,yfix:F,kfix:KF,ylam:V,klam:K))
def felse3(ymain:V,kmain:K,yfix:F,kfix:KF,ylam:V,klam:K): Fun[(Unit)] = term("felse3",List(ymain:V,kmain:K,yfix:F,kfix:KF,ylam:V,klam:K))
def fif2(ymain:V,kmain:K,yfix:F,kfix:KF,ylam:V,klam:K): Fun[V0]       = term("fif2",List(ymain:V,kmain:K,yfix:F,kfix:KF,ylam:V,klam:K))
def fapp0(ymain:V,kmain:K): Fun[V0]                                   = term("fapp0",List(ymain:V,kmain:K))
def XXfix(f:Fun[(F0,KF0)]): Fun[(V0,K0)]                              = term("XXfix",List(f:Fun[(F0,KF0)]))
def XXpart(x:V,k:K): Fun[F0]                                          = term("XXpart",List(x:V,k:K))
def XXtop(): Fun[V0]                                                  = term("XXtop",List())

def unit(): Exp[Unit] = term("unit",Nil)
def mult(x: Exp[Int], y: Exp[Int], z: Exp[Int]): Rel = add(x,y,z) // don't have relational mult atm
def isZero(x: Exp[Int]): Rel = (x === zero)
def nonZero(x: Exp[Int]): Rel = exists[Int] { n => x === succ(n) }


def runv(q1: Exp[Int], q2: Exp[Int]): Rel = 
  runfw(pair(main0(),pair(q1,XXtop())), pair(XXtop(),q2))

def runb(q1: Exp[Int], q2: Exp[Int]): Rel = 
  runbw(pair(main0(),pair(q1,XXtop())), pair(XXtop(),q2))

def runfw(st0: Exp[Any], st1: Exp[Any]): Rel = 
  (st0 === st1) || exists[Any] { stx => step(st0, stx) && runfw(stx,st1) }

def runbw(st0: Exp[Any], st1: Exp[Any]): Rel = 
  (st0 === st1) || exists[Any] { stx => step(stx, st1) && runbw(st0,stx) }


def step[T](st0:Exp[Any], st1: Exp[Any]): Rel = {
  def call[T](f: Fun[T], x: Exp[T]): Rel = st1 === pair(f,x)
  def exec[T](f: Fun[T], x: Exp[T]): Rel =
    //case (fthen3(ymain:V,kmain:K,yfix:F,kfix:KF,ylam:V,klam:K), ()) =>
    //  val xp = ylam + -1
    //  yfix(xp,fapp3(ymain,kmain,yfix,kfix,ylam,klam))
    (exists { (ymain:V,kmain:K,yfix:F,kfix:KF,ylam:V,klam:K) => 
      (f === fthen3(ymain:V,kmain:K,yfix:F,kfix:KF,ylam:V,klam:K)) && (x === unit()) &&
      exists { (xp:V) =>
        add(xp,1,ylam) &&
        call(yfix, (xp,fapp3(ymain,kmain,yfix,kfix,ylam,klam)))
      }
    }) ||
    //case (fapp3(ymain:V,kmain:K,yfix:F,kfix:KF,ylam:V,klam:K), yapp: V) =>
    //  val xt = ylam * yapp
    //  fif2(ymain,kmain,yfix,kfix,ylam,klam)(xt)
    (exists { (ymain:V,kmain:K,yfix:F,kfix:KF,ylam:V,klam:K,  yapp:V) => 
      (f === fapp3(ymain:V,kmain:K,yfix:F,kfix:KF,ylam:V,klam:K)) && (x === (yapp:V)) &&
      exists { (xt: V) =>
        mult(ylam,yapp,xt) &&
        call(fif2(ymain,kmain,yfix,kfix,ylam,klam), xt)
      }
    }) ||
    //case (felse3(ymain:V,kmain:K,yfix:F,kfix:KF,ylam:V,klam:K), ()) =>
    //  fif2(ymain,kmain,yfix,kfix,ylam,klam)(1)
    exists { (ymain:V,kmain:K,yfix:F,kfix:KF,ylam:V,klam:K) =>
      (f === felse3(ymain:V,kmain:K,yfix:F,kfix:KF,ylam:V,klam:K)) && (x === unit()) &&
      call(fif2(ymain,kmain,yfix,kfix,ylam,klam), 1)
    } ||
    //case (flam2(ymain:V,kmain:K,yfix:F,kfix:KF), (ylam:V,klam:K)) =>
    //  if (ylam != 0) fthen3(ymain,kmain,yfix,kfix,ylam,klam)() 
    //  else felse3(ymain,kmain,yfix,kfix,ylam,klam)()
    exists { (ymain:V,kmain:K,yfix:F,kfix:KF, ylam:V,klam:K) =>
      (f === flam2(ymain:V,kmain:K,yfix:F,kfix:KF)) && (x === (ylam:V,klam:K)) &&
      ({ isZero(ylam)  && call(felse3(ymain,kmain,yfix,kfix,ylam,klam), unit()) } ||
       { nonZero(ylam) && call(fthen3(ymain,kmain,yfix,kfix,ylam,klam), unit()) })
    } ||
    //case (fif2(ymain:V,kmain:K,yfix:F,kfix:KF,ylam:V,klam:K), yif: V) =>
    //  klam(yif)
    exists { (ymain:V,kmain:K,yfix:F,kfix:KF,ylam:V,klam:K, yif: V) =>
      (f === fif2(ymain:V,kmain:K,yfix:F,kfix:KF,ylam:V,klam:K)) && (x === (yif: V)) &&
      call(klam, yif)
    } ||
    //case (ffix1(ymain:V,kmain:K), (yfix:F,kfix:KF)) =>
    //  kfix(flam2(ymain,kmain,yfix,kfix))
    exists { (ymain:V,kmain:K, yfix:F,kfix:KF) =>
      (f === ffix1(ymain:V,kmain:K)) && (x === (yfix:F,kfix:KF)) &&
      call(kfix, flam2(ymain,kmain,yfix,kfix))
    } ||
    //case (main0(), (ymain:V,kmain:K)) =>
    //  fclos(ffix1(ymain,kmain))(ymain,fapp0(ymain,kmain))
    exists { (ymain:V,kmain:K) =>
      (f === main0()) && (x === (ymain:V,kmain:K)) &&
      call(XXfix(ffix1(ymain,kmain)), (ymain,fapp0(ymain,kmain)))
    } ||
    //case (fapp0(ymain:V,kmain:K), yapp: V) =>
    //  kmain(yapp)
    exists { (ymain:V,kmain:K, yapp: V) =>
      (f === fapp0(ymain:V,kmain:K)) && (x === (yapp: V)) &&
      call(kmain, yapp)
    } ||
    //case (f1@XXfix(f:(((F,KF))=>R)), (x:V,k:K)) =>
    //  //f((f1, f2 => f2(x,k)))
    //  f((f1,XXpart(x,k)))
    exists { (f1:Fun[(F0,KF0)], x1:V,k1:K) =>
      (f === XXfix(f1)) && (x === (x1,k1)) &&
      call(f1, (f.asInstanceOf[Fun[(V0,K0)]], XXpart(x1,k1)))
    } ||
    //case (XXpart(x,k), (f:F)) =>
    //  f(x,k)
    exists { (x1:V,k1:K, f1:F)  =>
      (f === XXpart(x1,k1)) && (x === (f1:F)) &&
      call(f1, (x1,k1))
    } //||
    //case (XXtop(), y:V) => // not handled here!
    //  exit(y)
    /*{
      (f === XXtop()) && (q === x) // set result
    }*/

  exists { (f:Fun[T],x:Exp[T]) => (st0 === (f,x)) && exec(f,x) }
}


}






/*
call main0() -- (4,XXtop())
call XXfix(ffix1(4,XXtop())) -- (4,fapp0(4,XXtop()))
call ffix1(4,XXtop()) -- (XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())))
call XXpart(4,fapp0(4,XXtop())) -- flam2(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())))
call flam2(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop()))) -- (4,fapp0(4,XXtop()))
call fthen3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())) -- ()
call XXfix(ffix1(4,XXtop())) -- (3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))
call ffix1(4,XXtop()) -- (XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))))
call XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))) -- flam2(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))))
call flam2(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))) -- (3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))
call fthen3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))) -- ()
call XXfix(ffix1(4,XXtop())) -- (2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))))
call ffix1(4,XXtop()) -- (XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))))
call XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))) -- flam2(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))))
call flam2(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))))) -- (2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))))
call fthen3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))) -- ()
call XXfix(ffix1(4,XXtop())) -- (1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))))
call ffix1(4,XXtop()) -- (XXfix(ffix1(4,XXtop())),XXpart(1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))))))
call XXpart(1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))))) -- flam2(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))))))
call flam2(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))))) -- (1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))))
call fthen3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))))),1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))))) -- ()
call XXfix(ffix1(4,XXtop())) -- (0,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))))),1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))))))
call ffix1(4,XXtop()) -- (XXfix(ffix1(4,XXtop())),XXpart(0,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))))),1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))))))
call XXpart(0,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))))),1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))))) -- flam2(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(0,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))))),1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))))))
call flam2(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(0,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))))),1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))))))) -- (0,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))))),1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))))))
call felse3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(0,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))))),1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))))),0,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))))),1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))))) -- ()
call fif2(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(0,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))))),1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))))),0,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))))),1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))))) -- 1
call fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))))),1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))))) -- 1
call fif2(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))))),1,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))))) -- 1
call fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))) -- 1
call fif2(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))),2,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())))) -- 2
call fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))) -- 2
call fif2(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))),3,fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop()))) -- 6
call fapp3(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())) -- 6
call fif2(4,XXtop(),XXfix(ffix1(4,XXtop())),XXpart(4,fapp0(4,XXtop())),4,fapp0(4,XXtop())) -- 24
call fapp0(4,XXtop()) -- 24
call XXtop() -- 24
*/


}
