package scalogno

class Exe(command: String) {

  import scala.sys.process._
  import scala.io._
  import java.io._
  import scala.concurrent._

  val inputStream = new SyncVar[OutputStream]
  val outputStream = new SyncVar[BufferedReader]

  val process = Process(command).run(
    new ProcessIO(
      stdin => inputStream.put(stdin),
      stdout => outputStream.put(new BufferedReader(new InputStreamReader(stdout))),
      stderr => Source.fromInputStream(stderr).getLines.foreach(println)));

  def readLine(): String = synchronized {
    outputStream.get.readLine()
  }

  def write(s: String): Unit = synchronized {
    inputStream.get.write((s + "\n").getBytes)
  }

  def close(): Unit = {
    inputStream.get.close
    outputStream.get.close
  }
}

trait SmtShell
object Play extends SmtShell

