name := "scalogno"

version := "0.3"

scalaVersion := "2.12.6"

libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.5" % "test"

parallelExecution in Test := false

initialCommands in console := "import scalogno.Play._"
