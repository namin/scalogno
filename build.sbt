name := "scalogno"

version := "0.1"

scalaOrganization := "org.scala-lang.virtualized"

scalaVersion := "2.10.2-RC1"

scalacOptions += "-Yvirtualize"

scalacOptions += "-Xexperimental"

scalacOptions += "-deprecation"

scalacOptions += "-unchecked"

scalacOptions += "-feature"

libraryDependencies += "org.scala-lang.virtualized" % "scala-compiler" % "2.10.2-RC1"

libraryDependencies += "org.scalatest" %% "scalatest" % "1.9.1" % "test"

libraryDependencies += "junit" % "junit" % "4.11" % "test"

unmanagedJars in Compile += file("../ScalaZ3/lib-bin/libscalaz3.so")

libraryDependencies += "ch.epfl.lara" % "scalaz3_2.10" % "2.0"

parallelExecution in Test := false
