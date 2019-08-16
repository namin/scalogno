name := "scalogno"

version := "0.3"

scalaVersion := "2.13.0"

libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.8" % "test"

parallelExecution in Test := false

initialCommands in console := "import scalogno.Play._"
