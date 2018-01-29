name := "scalogno"

version := "0.1"

scalaVersion := "2.11.2"

scalaOrganization := "org.scala-lang.virtualized"

resolvers += Resolver.sonatypeRepo("snapshots")

scalacOptions += "-Yvirtualize"

scalacOptions += "-Xexperimental"

scalacOptions += "-deprecation"

scalacOptions += "-unchecked"

scalacOptions += "-feature"


libraryDependencies += "org.scala-lang.lms" %% "lms-core" % "1.0.0-SNAPSHOT"

libraryDependencies += "org.scala-lang.virtualized" % "scala-compiler" % "2.11.2"

libraryDependencies += "org.scala-lang.virtualized" % "scala-library" % "2.11.2"

libraryDependencies += "org.scala-lang.virtualized" % "scala-reflect" % "2.11.2"

libraryDependencies += "org.scalatest" % "scalatest_2.11" % "2.2.2"

libraryDependencies += "junit" % "junit" % "4.11" % "test"

unmanagedJars in Compile += {
  val platform = ("uname" !!) stripLineEnd
  val extlib = Map("Linux" -> "so", "Darwin" -> "dylib")(platform)
  file("../ScalaZ3/lib-bin/libscalaz3."+extlib)
}

libraryDependencies += "ch.epfl.lara" % "scalaz3_2.11" % "3.0"

parallelExecution in Test := false
