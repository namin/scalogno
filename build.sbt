name := "scalogno"

version := "0.4"

scalaVersion := "2.13.6"

libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.9" % "test"

parallelExecution in Test := false

initialCommands in console := "import scalogno.Play._"
