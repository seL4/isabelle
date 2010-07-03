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
      ('C' : Int) -> Markup.WRITELN,
      ('D' : Int) -> Markup.TRACING,
      ('E' : Int) -> Markup.WARNING,
      ('F' : Int) -> Markup.ERROR,
      ('G' : Int) -> Markup.DEBUG)
    def is_raw(kind: String) =
      kind == Markup.STDOUT
    def is_control(kind: String) =
      kind == Markup.SYSTEM ||
      kind == Markup.SIGNAL ||
      kind == Markup.EXIT
    def is_system(kind: String) =
      kind == Markup.SYSTEM ||
      kind == Markup.STDIN ||
      kind == Markup.SIGNAL ||
      kind == Markup.EXIT ||
      kind == Markup.STATUS
  }

  class Result(val message: XML.Elem)
  {
    def kind = message.name
    def body = message.body

    def is_raw = Kind.is_raw(kind)
    def is_control = Kind.is_control(kind)
    def is_system = Kind.is_system(kind)
    def is_status = kind == Markup.STATUS
    def is_ready = is_status && body == List(XML.Elem(Markup.READY, Nil, Nil))

    override def toString: String =
    {
      val res =
        if (is_status) message.body.map(_.toString).mkString
        else Pretty.string_of(message.body)
      val props = message.attributes
      if (props.isEmpty)
        kind.toString + " [[" + res + "]]"
      else
        kind.toString + " " +
          (for ((x, y) <- props) yield x + "=" + y).mkString("{", ",", "}") + " [[" + res + "]]"
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
    receiver ! new Result(XML.Elem(kind, props, body))
  }

  private def put_result(kind: String, text: String)
  {
    put_result(kind, Nil, List(XML.Text(system.symbols.decode(text))))
  }


  /* signals */

  def interrupt() = synchronized {
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

  def kill() = synchronized {
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

  private class Stdin_Thread(out_stream: OutputStream) extends Thread("isabelle: stdin") {
    override def run() = {
      val writer = new BufferedWriter(new OutputStreamWriter(out_stream, Standard_System.charset))
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
            put_result(Markup.STDIN, s)
            writer.write(s)
            writer.flush
          }
          //}}}
        }
        catch {
          case e: IOException => put_result(Markup.SYSTEM, "Stdin thread: " + e.getMessage)
        }
      }
      put_result(Markup.SYSTEM, "Stdin thread terminated")
    }
  }


  /* stdout */

  private class Stdout_Thread(in_stream: InputStream) extends Thread("isabelle: stdout") {
    override def run() = {
      val reader = new BufferedReader(new InputStreamReader(in_stream, Standard_System.charset))
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
            put_result(Markup.STDOUT, result.toString)
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
          case e: IOException => put_result(Markup.SYSTEM, "Stdout thread: " + e.getMessage)
        }
      }
      put_result(Markup.SYSTEM, "Stdout thread terminated")
    }
  }


  /* messages */

  private class Message_Thread(fifo: String) extends Thread("isabelle: messages")
  {
    private class Protocol_Error(msg: String) extends Exception(msg)
    override def run()
    {
      val stream = system.fifo_stream(fifo)
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
              case List(XML.Elem(name, props, Nil))
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

      put_result(Markup.SYSTEM, "Message thread terminated")
    }
  }



  /** main **/

  {
    /* messages */

    val message_fifo = system.mk_fifo()
    def rm_fifo() = system.rm_fifo(message_fifo)

    val message_thread = new Message_Thread(message_fifo)
    message_thread.start


    /* exec process */

    try {
      val cmdline = List(system.getenv_strict("ISABELLE_PROCESS"), "-W", message_fifo) ++ args
      proc = system.execute(true, cmdline: _*)
    }
    catch {
      case e: IOException =>
        rm_fifo()
        error("Failed to execute Isabelle process: " + e.getMessage)
    }


    /* stdin/stdout */

    new Stdin_Thread(proc.getOutputStream).start
    new Stdout_Thread(proc.getInputStream).start


    /* exit */

    new Thread("isabelle: exit") {
      override def run() = {
        val rc = proc.waitFor()
        Thread.sleep(300)  // FIXME property!?
        put_result(Markup.SYSTEM, "Exit thread terminated")
        put_result(Markup.EXIT, rc.toString)
        rm_fifo()
      }
    }.start
  }
}
