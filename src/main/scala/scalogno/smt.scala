package scalogno

class SmtSolver {
  var smt: Exe = _
  def init() = {
    smt = new Exe("cvc4 --interactive --lang smt")
    smt.skipHeader()
    smt.write("(set-logic ALL_SUPPORTED)")
  }
  def add(c: Any): Unit = {} // TODO
  def checkSat(): Boolean = true // TODO
  def push(): Unit = smt.write("(push)")
  def pop(): Unit = smt.write("(pop)")
  def extractModel(): Unit = {} // TODO
}

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

  def skipHeader() = synchronized {
    (0 until 24/*brittle magic*/).foreach{_ => readLine()}
  }

  def readLine(): String = synchronized {
    outputStream.get.readLine()
  }

  def readAtom(): String = synchronized {
    readLine().replaceAll("CVC4> ", "")/*brittle magic*/
  }

  def readSExp(): String = synchronized {
    var sb = new StringBuffer()
    var pl = 0
    var pr = 0
    def processLine() = {
      val line = readLine()
      pl += line.count(_ == '(')
      pr += line.count(_ == ')')
      sb.append(line)
    }
    var first = true;
    while (first || (pr == pr)) {
      processLine()
      first = false
    }
    sb.toString
  }

  def write(s: String): Unit = synchronized {
    inputStream.get.write((s + "\n\n").getBytes)
    inputStream.get.flush()
  }

  def close(): Unit = {
    inputStream.get.close
    outputStream.get.close
  }
}

object Play extends Base with Engine
