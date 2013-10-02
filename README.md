scalogno
========

Prototyping logic programming in Scala.

ScalaZ3 Setup
-------------

* Set up
  [https://github.com/epfl-lara/ScalaZ3](https://github.com/epfl-lara/ScalaZ3)
  in a sibling directory.

* From ScalaZ3, `sbt publish-local`.

* For Mac OS X, I find it necessary to start `sbt` as such: `DYLD_LIBRARY_PATH=../ScalaZ3/z3/4.3-osx-64b/lib sbt`
