/*  Title:      Pure/System/isabelle_process.ML
    Author:     Makarius
    Options:    :folding=explicit:collapseFolds=1:

Isabelle process management -- always reactive due to multi-threaded I/O.
*/

package isabelle

import java.util.concurrent.LinkedBlockingQueue
import java.io.{BufferedReader, BufferedWriter, InputStreamReader, OutputStreamWriter,
  InputStream, OutputStream, IOException}


object Isabelle_Process {

  /* results */

  object Kind extends Enumeration {
    //{{{ values and codes
    // internal system notification
    val SYSTEM = Value("SYSTEM")
    // Posix channels/events
    val STDIN = Value("STDIN")
    val STDOUT = Value("STDOUT")
    val SIGNAL = Value("SIGNAL")
    val EXIT = Value("EXIT")
    // Isabelle messages
    val INIT = Value("INIT")
    val STATUS = Value("STATUS")
    val WRITELN = Value("WRITELN")
    val PRIORITY = Value("PRIORITY")
    val TRACING = Value("TRACING")
    val WARNING = Value("WARNING")
    val ERROR = Value("ERROR")
    val DEBUG = Value("DEBUG")
    // messages codes
    val code = Map(
      ('A' : Int) -> Kind.INIT,
      ('B' : Int) -> Kind.STATUS,
      ('C' : Int) -> Kind.WRITELN,
      ('D' : Int) -> Kind.PRIORITY,
      ('E' : Int) -> Kind.TRACING,
      ('F' : Int) -> Kind.WARNING,
      ('G' : Int) -> Kind.ERROR,
      ('H' : Int) -> Kind.DEBUG,
      ('0' : Int) -> Kind.SYSTEM,
      ('1' : Int) -> Kind.STDIN,
      ('2' : Int) -> Kind.STDOUT,
      ('3' : Int) -> Kind.SIGNAL,
      ('4' : Int) -> Kind.EXIT)
    // message markup
    val markup = Map(
      Kind.INIT -> Markup.INIT,
      Kind.STATUS -> Markup.STATUS,
      Kind.WRITELN -> Markup.WRITELN,
      Kind.PRIORITY -> Markup.PRIORITY,
      Kind.TRACING -> Markup.TRACING,
      Kind.WARNING -> Markup.WARNING,
      Kind.ERROR -> Markup.ERROR,
      Kind.DEBUG -> Markup.DEBUG,
      Kind.SYSTEM -> Markup.SYSTEM,
      Kind.STDIN -> Markup.STDIN,
      Kind.STDOUT -> Markup.STDOUT,
      Kind.SIGNAL -> Markup.SIGNAL,
      Kind.EXIT -> Markup.EXIT)
    //}}}
    def is_raw(kind: Value) =
      kind == STDOUT
    def is_control(kind: Value) =
      kind == SYSTEM ||
      kind == SIGNAL ||
      kind == EXIT
    def is_system(kind: Value) =
      kind == SYSTEM ||
      kind == STDIN ||
      kind == SIGNAL ||
      kind == EXIT ||
      kind == STATUS
  }

  class Result(val kind: Kind.Value, val props: List[(String, String)], val result: String) {
    override def toString = {
      val trees = YXML.parse_body_failsafe(result)
      val res =
        if (kind == Kind.STATUS) trees.map(_.toString).mkString
        else trees.flatMap(XML.content(_).mkString).mkString
      if (props.isEmpty)
        kind.toString + " [[" + res + "]]"
      else
        kind.toString + " " +
          (for ((x, y) <- props) yield x + "=" + y).mkString("{", ",", "}") + " [[" + res + "]]"
    }
    def is_raw = Kind.is_raw(kind)
    def is_control = Kind.is_control(kind)
    def is_system = Kind.is_system(kind)
  }

  def parse_message(isabelle_system: Isabelle_System, result: Result) =
  {
    XML.Elem(Markup.MESSAGE, (Markup.CLASS, Kind.markup(result.kind)) :: result.props,
      YXML.parse_body_failsafe(isabelle_system.symbols.decode(result.result)))
  }
}


class Isabelle_Process(isabelle_system: Isabelle_System,
  results: EventBus[Isabelle_Process.Result], args: String*)
{
  import Isabelle_Process._


  /* demo constructor */

  def this(args: String*) =
    this(new Isabelle_System, new EventBus[Isabelle_Process.Result] + Console.println, args: _*)


  /* process information */

  @volatile private var proc: Process = null
  @volatile private var closing = false
  @volatile private var pid: String = null
  @volatile private var the_session: String = null
  def session = the_session


  /* results */

  def parse_message(result: Result): XML.Tree =
    Isabelle_Process.parse_message(isabelle_system, result)

  private val result_queue = new LinkedBlockingQueue[Result]

  private def put_result(kind: Kind.Value, props: List[(String, String)], result: String)
  {
    if (kind == Kind.INIT) {
      val map = Map(props: _*)
      if (map.isDefinedAt(Markup.PID)) pid = map(Markup.PID)
      if (map.isDefinedAt(Markup.SESSION)) the_session = map(Markup.SESSION)
    }
    result_queue.put(new Result(kind, props, result))
  }

  private class ResultThread extends Thread("isabelle: results") {
    override def run() = {
      var finished = false
      while (!finished) {
        val result =
          try { result_queue.take }
          catch { case _: NullPointerException => null }

        if (result != null) {
          results.event(result)
          if (result.kind == Kind.EXIT) finished = true
        }
        else finished = true
      }
    }
  }


  /* signals */

  def interrupt() = synchronized {
    if (proc == null) error("Cannot interrupt Isabelle: no process")
    if (pid == null) put_result(Kind.SYSTEM, Nil, "Cannot interrupt: unknown pid")
    else {
      try {
        if (isabelle_system.execute(true, "kill", "-INT", pid).waitFor == 0)
          put_result(Kind.SIGNAL, Nil, "INT")
        else
          put_result(Kind.SYSTEM, Nil, "Cannot interrupt: kill command failed")
      }
      catch { case e: IOException => error("Cannot interrupt Isabelle: " + e.getMessage) }
    }
  }

  def kill() = synchronized {
    if (proc == 0) error("Cannot kill Isabelle: no process")
    else {
      try_close()
      Thread.sleep(500)
      put_result(Kind.SIGNAL, Nil, "KILL")
      proc.destroy
      proc = null
      pid = null
    }
  }


  /* output being piped into the process */

  private val output = new LinkedBlockingQueue[String]

  private def output_raw(text: String) = synchronized {
    if (proc == null) error("Cannot output to Isabelle: no process")
    if (closing) error("Cannot output to Isabelle: already closing")
    output.put(text)
  }

  def output_sync(text: String) =
    output_raw(" \\<^sync>\n; " + text + " \\<^sync>;\n")


  def command(text: String) =
    output_sync("Isabelle.command " + Isabelle_Syntax.encode_string(text))

  def command(props: List[(String, String)], text: String) =
    output_sync("Isabelle.command " + Isabelle_Syntax.encode_properties(props) + " " +
      Isabelle_Syntax.encode_string(text))

  def ML(text: String) =
    output_sync("ML_val " + Isabelle_Syntax.encode_string(text))

  def close() = synchronized {    // FIXME watchdog/timeout
    output_raw("\u0000")
    closing = true
  }

  def try_close() = synchronized {
    if (proc != null && !closing) {
      try { close() }
      catch { case _: RuntimeException => }
    }
  }


  /* stdin */

  private class StdinThread(out_stream: OutputStream) extends Thread("isabelle: stdin") {
    override def run() = {
      val writer = new BufferedWriter(new OutputStreamWriter(out_stream, Isabelle_System.charset))
      var finished = false
      while (!finished) {
        try {
          //{{{
          val s = output.take
          if (s == "\u0000") {
            writer.close
            finished = true
          }
          else {
            put_result(Kind.STDIN, Nil, s)
            writer.write(s)
            writer.flush
          }
          //}}}
        }
        catch {
          case e: IOException => put_result(Kind.SYSTEM, Nil, "Stdin thread: " + e.getMessage)
        }
      }
      put_result(Kind.SYSTEM, Nil, "Stdin thread terminated")
    }
  }


  /* stdout */

  private class StdoutThread(in_stream: InputStream) extends Thread("isabelle: stdout") {
    override def run() = {
      val reader = new BufferedReader(new InputStreamReader(in_stream, Isabelle_System.charset))
      var result = new StringBuilder(100)

      var finished = false
      while (!finished) {
        try {
          //{{{
          var c = -1
          var done = false
          while (!done && (result.length == 0 || reader.ready)) {
            c = reader.read
            if (c >= 0) result.append(c.asInstanceOf[Char])
            else done = true
          }
          if (result.length > 0) {
            put_result(Kind.STDOUT, Nil, result.toString)
            result.length = 0
          }
          else {
            reader.close
            finished = true
            try_close()
          }
          //}}}
        }
        catch {
          case e: IOException => put_result(Kind.SYSTEM, Nil, "Stdout thread: " + e.getMessage)
        }
      }
      put_result(Kind.SYSTEM, Nil, "Stdout thread terminated")
    }
  }


  /* messages */

  private class MessageThread(fifo: String) extends Thread("isabelle: messages") {
    override def run() = {
      val reader = isabelle_system.fifo_reader(fifo)
      var kind: Kind.Value = null
      var props: List[(String, String)] = Nil
      var result = new StringBuilder

      var finished = false
      while (!finished) {
        try {
          if (kind == null) {
            //{{{ Char mode -- resync
            var c = -1
            do {
              c = reader.read
              if (c >= 0 && c != 2) result.append(c.asInstanceOf[Char])
            } while (c >= 0 && c != 2)

            if (result.length > 0) {
              put_result(Kind.SYSTEM, Nil, "Malformed message:\n" + result.toString)
              result.length = 0
            }
            if (c < 0) {
              reader.close
              finished = true
              try_close()
            }
            else {
              c = reader.read
              if (Kind.code.isDefinedAt(c)) kind = Kind.code(c)
              else kind = null
            }
            //}}}
          }
          else {
            //{{{ Line mode
            val line = reader.readLine
            if (line == null) {
              reader.close
              finished = true
              try_close()
            }
            else {
              val len = line.length
              // property
              if (line.endsWith("\u0002,")) {
                val i = line.indexOf('=')
                if (i > 0) {
                  val name = line.substring(0, i)
                  val value = line.substring(i + 1, len - 2)
                  props = (name, value) :: props
                }
              }
              // last text line
              else if (line.endsWith("\u0002.")) {
                result.append(line.substring(0, len - 2))
                put_result(kind, props.reverse, result.toString)
                kind = null
                props = Nil
                result.length = 0
              }
              // text line
              else {
                result.append(line)
                result.append('\n')
              }
            }
            //}}}
          }
        }
        catch {
          case e: IOException => put_result(Kind.SYSTEM, Nil, "Message thread: " + e.getMessage)
        }
      }
      put_result(Kind.SYSTEM, Nil, "Message thread terminated")
    }
  }



  /** main **/

  {
    /* isabelle version */

    {
      val (msg, rc) = isabelle_system.isabelle_tool("version")
      if (rc != 0) error("Version check failed -- bad Isabelle installation:\n" + msg)
      put_result(Kind.SYSTEM, Nil, msg)
    }


    /* messages */

    val message_fifo = isabelle_system.mk_fifo()
    def rm_fifo() = isabelle_system.rm_fifo(message_fifo)

    val message_thread = new MessageThread(message_fifo)
    message_thread.start

    new ResultThread().start


    /* exec process */

    try {
      val cmdline =
        List(isabelle_system.getenv_strict("ISABELLE_PROCESS"), "-W", message_fifo) ++ args
      proc = isabelle_system.execute(true, cmdline: _*)
    }
    catch {
      case e: IOException =>
        rm_fifo()
        error("Failed to execute Isabelle process: " + e.getMessage)
    }


    /* stdin/stdout */

    new StdinThread(proc.getOutputStream).start
    new StdoutThread(proc.getInputStream).start


    /* exit */

    new Thread("isabelle: exit") {
      override def run() = {
        val rc = proc.waitFor()
        Thread.sleep(300)
        put_result(Kind.SYSTEM, Nil, "Exit thread terminated")
        put_result(Kind.EXIT, Nil, Integer.toString(rc))
        rm_fifo()
      }
    }.start

  }
}
