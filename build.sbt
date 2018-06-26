name := "scalogno"

version := "0.2"

scalaVersion := "2.12.4"

libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.4" % "test"

parallelExecution in Test := false

initialCommands in console := "import scalogno.Play._"
