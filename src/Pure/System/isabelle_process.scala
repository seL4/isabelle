/*  Title:      Pure/System/isabelle_process.ML
    Author:     Makarius
    Options:    :folding=explicit:collapseFolds=1:

Isabelle process management -- always reactive due to multi-threaded I/O.
*/

package isabelle

import java.util.concurrent.LinkedBlockingQueue
import java.io.{BufferedReader, BufferedWriter, InputStreamReader, OutputStreamWriter,
  InputStream, OutputStream, IOException}

import scala.actors.Actor
import Actor._


object Isabelle_Process
{
  /* results */

  object Kind {
    // message markup
    val markup = Map(
      ('A' : Int) -> Markup.INIT,
      ('B' : Int) -> Markup.STATUS,
      ('C' : Int) -> Markup.REPORT,
      ('D' : Int) -> Markup.WRITELN,
      ('E' : Int) -> Markup.TRACING,
      ('F' : Int) -> Markup.WARNING,
      ('G' : Int) -> Markup.ERROR,
      ('H' : Int) -> Markup.DEBUG)
    def is_raw(kind: String) =
      kind == Markup.STDOUT
    def is_control(kind: String) =
      kind == Markup.SYSTEM ||
      kind == Markup.SIGNAL ||
      kind == Markup.EXIT
    def is_system(kind: String) =
      kind == Markup.SYSTEM ||
      kind == Markup.INPUT ||
      kind == Markup.STDIN ||
      kind == Markup.SIGNAL ||
      kind == Markup.EXIT ||
      kind == Markup.STATUS
  }

  class Result(val message: XML.Elem)
  {
    def kind = message.markup.name
    def properties = message.markup.properties
    def body = message.body

    def is_raw = Kind.is_raw(kind)
    def is_control = Kind.is_control(kind)
    def is_system = Kind.is_system(kind)
    def is_status = kind == Markup.STATUS
    def is_report = kind == Markup.REPORT
    def is_ready = is_status && body == List(XML.Elem(Markup.Ready, Nil))

    override def toString: String =
    {
      val res =
        if (is_status || is_report) message.body.map(_.toString).mkString
        else Pretty.string_of(message.body)
      if (properties.isEmpty)
        kind.toString + " [[" + res + "]]"
      else
        kind.toString + " " +
          (for ((x, y) <- properties) yield x + "=" + y).mkString("{", ",", "}") + " [[" + res + "]]"
    }

    def cache(c: XML.Cache): Result = new Result(c.cache_tree(message).asInstanceOf[XML.Elem])
  }
}


class Isabelle_Process(system: Isabelle_System, receiver: Actor, args: String*)
{
  import Isabelle_Process._


  /* demo constructor */

  def this(args: String*) =
    this(new Isabelle_System,
      actor { loop { react { case res => Console.println(res) } } }, args: _*)


  /* process information */

  @volatile private var proc: Process = null
  @volatile private var closing = false
  @volatile private var pid: String = null


  /* results */

  private def put_result(kind: String, props: List[(String, String)], body: List[XML.Tree])
  {
    if (kind == Markup.INIT) {
      for ((Markup.PID, p) <- props) pid = p
    }
    receiver ! new Result(XML.Elem(Markup(kind, props), body))
  }

  private def put_result(kind: String, text: String)
  {
    put_result(kind, Nil, List(XML.Text(system.symbols.decode(text))))
  }


  /* signals */

  def interrupt() = synchronized {  // FIXME avoid synchronized
    if (proc == null) error("Cannot interrupt Isabelle: no process")
    if (pid == null) put_result(Markup.SYSTEM, "Cannot interrupt: unknown pid")
    else {
      try {
        if (system.execute(true, "kill", "-INT", pid).waitFor == 0)
          put_result(Markup.SIGNAL, "INT")
        else
          put_result(Markup.SYSTEM, "Cannot interrupt: kill command failed")
      }
      catch { case e: IOException => error("Cannot interrupt Isabelle: " + e.getMessage) }
    }
  }

  def kill() = synchronized {  // FIXME avoid synchronized
    if (proc == 0) error("Cannot kill Isabelle: no process")
    else {
      try_close()
      Thread.sleep(500)  // FIXME property!?
      put_result(Markup.SIGNAL, "KILL")
      proc.destroy
      proc = null
      pid = null
    }
  }



  /** stream actors **/

  /* input */

  case class Input(cmd: String)
  case object Close

  private def input_actor(name: String, kind: String, stream: => OutputStream): Actor =
    Library.thread_actor(name) {
      val writer = new BufferedWriter(new OutputStreamWriter(stream, Standard_System.charset))
      var finished = false
      while (!finished) {
        try {
          //{{{
          receive {
            case Input(text) =>
              put_result(kind, text)
              writer.write(text)
              writer.flush
            case Close =>
              writer.close
              finished = true
            case bad => System.err.println(name + ": ignoring bad message " + bad)
          }
          //}}}
        }
        catch {
          case e: IOException => put_result(Markup.SYSTEM, name + ": " + e.getMessage)
        }
      }
      put_result(Markup.SYSTEM, name + " terminated")
    }


  /* raw output */

  private def output_actor(name: String, kind: String, stream: => InputStream): Actor =
    Library.thread_actor(name) {
      val reader = new BufferedReader(new InputStreamReader(stream, Standard_System.charset))
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
            put_result(kind, result.toString)
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
          case e: IOException => put_result(Markup.SYSTEM, name + ": " + e.getMessage)
        }
      }
      put_result(Markup.SYSTEM, name + " terminated")
    }


  /* message output */

  private class Protocol_Error(msg: String) extends Exception(msg)

  private def message_actor(name: String, stream: InputStream): Actor =
    Library.thread_actor(name) {
      val default_buffer = new Array[Byte](65536)
      var c = -1

      def read_chunk(): List[XML.Tree] =
      {
        //{{{
        // chunk size
        var n = 0
        c = stream.read
        while (48 <= c && c <= 57) {
          n = 10 * n + (c - 48)
          c = stream.read
        }
        if (c != 10) throw new Protocol_Error("bad message chunk header")

        // chunk content
        val buf =
          if (n <= default_buffer.size) default_buffer
          else new Array[Byte](n)

        var i = 0
        var m = 0
        do {
          m = stream.read(buf, i, n - i)
          i += m
        } while (m > 0 && n > i)

        if (i != n) throw new Protocol_Error("bad message chunk content")

        YXML.parse_body_failsafe(YXML.decode_chars(system.symbols.decode, buf, 0, n))
        //}}}
      }

      do {
        try {
          //{{{
          c = stream.read
          var non_sync = 0
          while (c >= 0 && c != 2) {
            non_sync += 1
            c = stream.read
          }
          if (non_sync > 0)
            throw new Protocol_Error("lost synchronization -- skipping " + non_sync + " bytes")
          if (c == 2) {
            val header = read_chunk()
            val body = read_chunk()
            header match {
              case List(XML.Elem(Markup(name, props), Nil))
                  if name.size == 1 && Kind.markup.isDefinedAt(name(0)) =>
                put_result(Kind.markup(name(0)), props, body)
              case _ => throw new Protocol_Error("bad header: " + header.toString)
            }
          }
          //}}}
        }
        catch {
          case e: IOException =>
            put_result(Markup.SYSTEM, "Cannot read message:\n" + e.getMessage)
          case e: Protocol_Error =>
            put_result(Markup.SYSTEM, "Malformed message:\n" + e.getMessage)
        }
      } while (c != -1)
      stream.close
      try_close()

      put_result(Markup.SYSTEM, name + " terminated")
    }



  /** init **/

  /* exec process */

  private val in_fifo = system.mk_fifo()
  private val out_fifo = system.mk_fifo()
  private def rm_fifos() = { system.rm_fifo(in_fifo); system.rm_fifo(out_fifo) }

  try {
    val cmdline =
      List(system.getenv_strict("ISABELLE_PROCESS"), "-W", in_fifo + ":" + out_fifo) ++ args
    proc = system.execute(true, cmdline: _*)
  }
  catch {
    case e: IOException =>
      rm_fifos()
      error("Failed to execute Isabelle process: " + e.getMessage)
  }


  /* exit process */

  Library.thread_actor("process_exit") {
    val rc = proc.waitFor()
    Thread.sleep(300)  // FIXME property!?
    put_result(Markup.SYSTEM, "process_exit terminated")
    put_result(Markup.EXIT, rc.toString)
    rm_fifos()
  }


  /* I/O actors */

  private val standard_input =
    input_actor("standard_input", Markup.STDIN, proc.getOutputStream)

  private val command_input =
    input_actor("command_input", Markup.INPUT, system.fifo_output_stream(in_fifo))

  output_actor("standard_output", Markup.STDOUT, proc.getInputStream)
  message_actor("message_output", system.fifo_input_stream(out_fifo))



  /** main methods **/

  def input_raw(text: String) = standard_input ! Input(text)

  def input(text: String) = synchronized {  // FIXME avoid synchronized
    if (proc == null) error("Cannot output to Isabelle: no process")
    if (closing) error("Cannot output to Isabelle: already closing")
    command_input ! Input(" \\<^sync>\n; " + text + " \\<^sync>;\n")
  }

  def close() = synchronized {    // FIXME avoid synchronized
    command_input ! Close
    closing = true
  }

  def try_close() = synchronized {
    if (proc != null && !closing) {
      try { close() }
      catch { case _: RuntimeException => }
    }
  }
}
