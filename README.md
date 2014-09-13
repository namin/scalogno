scalogno
========

Prototyping logic programming in Scala.
Presentation with some highlights ([PDF](http://lampwww.epfl.ch/~amin/elf/scalogno-slides.pdf)).

Setup
-----

* On Mac OS X, ensure `gcc` is not an alias for `clang`
  * `gcc --version`
  
```
gcc (Homebrew gcc49 4.9.1) 4.9.1
Copyright (C) 2014 Free Software Foundation, Inc.
This is free software; see the source for copying conditions.  There is NO
warranty; not even for MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
```

  * continue with steps only if output looks like `clang`, e.g.

```
Apple LLVM version 5.1 (clang-503.0.40) (based on LLVM 3.4svn)
Target: x86_64-apple-darwin13.3.0
Thread model: posix
```

  * [`brew`](http://brew.sh/)` install gcc49`
  * `sudo mv /usr/bin/gcc /usr/bin/gcc-mac`
  * `ln -s /usr/local/bin/gcc-4.9 /usr/local/bin/gcc`
  * `sudo ln -s /usr/local/bin/gcc /usr/bin/gcc`

* Set up `z3` in sibling directory
  * `cd ..` (from this `scalogno` directory)
  * `git clone https://git01.codeplex.com/z3`
  * `cd z3`
  * `git checkout rc`
  * `python scripts/mk_make.py`
  * `cd build`
  * `make`
  * put `z3` on your path, e.g.
    * `cp z3 ~/bin` 
  * `cd ../../scalogno`

* Set up `ScalaZ3` in sibling directory
  * `cd ..` (from this `scalogno` directory)
  * `git clone https://github.com/epfl-lara/ScalaZ3.git`
  * `cd ScalaZ3`
  * link `z3`
    * on Linux 64bit:
      * `mkdir -p z3/4.3-unix-64b/lib`
      * `cp ../z3/build/libz3.so z3/4.3-unix-64b/lib`
      * `cp -r ../z3/src/api z3/4.3-unix-64-b/include`
    * on Mac OS X 64 bit:
      * `mkdir -p z3/4.3-osx-64b/lib`
      * `cp ../z3/build/libz3.dylib z3/4.3-osx-64b/lib`
      * `cp -r ../z3/src/api z3/4.3-osx-64-b/include`
  * `sbt package`
  * `sbt packageBin` (might not be necessary, but doesn't hurt)
  * `sbt publish-local`
  * `sbt test` (optional sanity check on Linux, but does not work for me on Mac OS X)
  * `cd ../scalogno`

* Run tests
  * on Linux:
    * `sbt test`
  * on Mac OS X:
    * `DYLD_LIBRARY_PATH=../ScalaZ3/z3/4.3-osx-64b/lib sbt test`
