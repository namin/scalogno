name := "scalogno"

version := "0.4"

scalaVersion := "2.13.8"

libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.11" % "test"

parallelExecution in Test := false

initialCommands in console := "import scalogno.Play._"
