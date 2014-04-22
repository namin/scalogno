scalogno
========

Prototyping logic programming in Scala.
Presentation with some highlights ([PDF](http://lampwww.epfl.ch/~amin/elf/scalogno-slides.pdf)).

ScalaZ3 Setup
-------------

* Set up
  [https://github.com/epfl-lara/ScalaZ3](https://github.com/epfl-lara/ScalaZ3)
  in a sibling directory.

* From ScalaZ3, `sbt publish-local`.

* For Mac OS X, I find it necessary to start `sbt` as such: `DYLD_LIBRARY_PATH=../ScalaZ3/lib-bin sbt`
