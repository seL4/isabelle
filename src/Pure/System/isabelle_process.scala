/*  Title:      Pure/System/isabelle_process.scala
    Author:     Makarius
    Options:    :folding=explicit:collapseFolds=1:

Isabelle process management -- always reactive due to multi-threaded I/O.
*/

package isabelle

import java.lang.System
import java.util.concurrent.LinkedBlockingQueue
import java.io.{BufferedReader, BufferedWriter, InputStreamReader, OutputStreamWriter,
  InputStream, OutputStream, BufferedOutputStream, IOException}

import scala.actors.Actor
import Actor._


object Isabelle_Process
{
  /* results */

  object Kind
  {
    val message_markup = Map(
      ('A' : Int) -> Markup.INIT,
      ('B' : Int) -> Markup.STATUS,
      ('C' : Int) -> Markup.REPORT,
      ('D' : Int) -> Markup.WRITELN,
      ('E' : Int) -> Markup.TRACING,
      ('F' : Int) -> Markup.WARNING,
      ('G' : Int) -> Markup.ERROR,
      ('H' : Int) -> Markup.RAW)
  }

  sealed abstract class Message

  class Input(name: String, args: List[String]) extends Message
  {
    override def toString: String =
      XML.Elem(Markup(Markup.PROVER_COMMAND, List((Markup.NAME, name))),
        args.map(s =>
          List(XML.Text("\n"), XML.elem(Markup.PROVER_ARG, YXML.parse_body(s)))).flatten).toString
  }

  class Result(val message: XML.Elem) extends Message
  {
    def kind: String = message.markup.name
    def properties: Properties.T = message.markup.properties
    def body: XML.Body = message.body

    def is_init = kind == Markup.INIT
    def is_exit = kind == Markup.EXIT
    def is_stdout = kind == Markup.STDOUT
    def is_system = kind == Markup.SYSTEM
    def is_status = kind == Markup.STATUS
    def is_report = kind == Markup.REPORT
    def is_raw = kind == Markup.RAW
    def is_ready = Isar_Document.is_ready(message)
    def is_syslog = is_init || is_exit || is_system || is_ready

    override def toString: String =
    {
      val res =
        if (is_status || is_report) message.body.map(_.toString).mkString
        else if (is_raw) "..."
        else Pretty.string_of(message.body)
      if (properties.isEmpty)
        kind.toString + " [[" + res + "]]"
      else
        kind.toString + " " +
          (for ((x, y) <- properties) yield x + "=" + y).mkString("{", ",", "}") + " [[" + res + "]]"
    }
  }
}


class Isabelle_Process(
    timeout: Time = Time.seconds(25),
    receiver: Isabelle_Process.Message => Unit = Console.println(_),
    args: List[String] = Nil)
{
  import Isabelle_Process._


  /* results */

  private def system_result(text: String)
  {
    receiver(new Result(XML.Elem(Markup(Markup.SYSTEM, Nil), List(XML.Text(text)))))
  }

  private val xml_cache = new XML.Cache()

  private def put_result(kind: String, props: Properties.T, body: XML.Body)
  {
    if (kind == Markup.INIT) system_channel.accepted()
    if (kind == Markup.RAW)
      receiver(new Result(XML.Elem(Markup(kind, props), body)))
    else {
      val msg = XML.Elem(Markup(kind, props), Isar_Document.clean_message(body))
      receiver(new Result(xml_cache.cache_tree(msg).asInstanceOf[XML.Elem]))
    }
  }

  private def put_result(kind: String, text: String)
  {
    put_result(kind, Nil, List(XML.Text(Symbol.decode(text))))
  }


  /* input actors */

  private case class Input_Text(text: String)
  private case class Input_Chunks(chunks: List[Array[Byte]])

  private case object Close
  private def close(p: (Thread, Actor))
  {
    if (p != null && p._1.isAlive) {
      p._2 ! Close
      p._1.join
    }
  }

  @volatile private var standard_input: (Thread, Actor) = null
  @volatile private var command_input: (Thread, Actor) = null


  /** process manager **/

  private val system_channel = System_Channel()

  private val process =
    try {
      val cmdline =
        Isabelle_System.getenv_strict("ISABELLE_PROCESS") ::
          (system_channel.isabelle_args ::: args)
      new Isabelle_System.Managed_Process(true, cmdline: _*)
    }
    catch { case e: IOException => system_channel.accepted(); throw(e) }

  val process_result =
    Simple_Thread.future("process_result") { process.join }

  private def terminate_process()
  {
    try { process.terminate }
    catch { case e: IOException => system_result("Failed to terminate Isabelle: " + e.getMessage) }
  }

  private val process_manager = Simple_Thread.fork("process_manager")
  {
    val (startup_failed, startup_output) =
    {
      val expired = System.currentTimeMillis() + timeout.ms
      val result = new StringBuilder(100)

      var finished: Option[Boolean] = None
      while (finished.isEmpty && System.currentTimeMillis() <= expired) {
        while (finished.isEmpty && process.stdout.ready) {
          val c = process.stdout.read
          if (c == 2) finished = Some(true)
          else result += c.toChar
        }
        if (process_result.is_finished) finished = Some(false)
        else Thread.sleep(10)
      }
      (finished.isEmpty || !finished.get, result.toString.trim)
    }
    system_result(startup_output)

    if (startup_failed) {
      put_result(Markup.EXIT, "Return code: 127")
      process.stdin.close
      Thread.sleep(300)
      terminate_process()
      process_result.join
    }
    else {
      val (command_stream, message_stream) = system_channel.rendezvous()

      standard_input = stdin_actor()
      val stdout = stdout_actor()
      command_input = input_actor(command_stream)
      val message = message_actor(message_stream)

      val rc = process_result.join
      system_result("process terminated")
      for ((thread, _) <- List(standard_input, stdout, command_input, message)) thread.join
      system_result("process_manager terminated")
      put_result(Markup.EXIT, "Return code: " + rc.toString)
    }
    system_channel.accepted()
  }


  /* management methods */

  def join() { process_manager.join() }

  def terminate()
  {
    close()
    system_result("Terminating Isabelle process")
    terminate_process()
  }



  /** stream actors **/

  /* raw stdin */

  private def stdin_actor(): (Thread, Actor) =
  {
    val name = "standard_input"
    Simple_Thread.actor(name) {
      var finished = false
      while (!finished) {
        try {
          //{{{
          receive {
            case Input_Text(text) =>
              process.stdin.write(text)
              process.stdin.flush
            case Close =>
              process.stdin.close
              finished = true
            case bad => System.err.println(name + ": ignoring bad message " + bad)
          }
          //}}}
        }
        catch { case e: IOException => system_result(name + ": " + e.getMessage) }
      }
      system_result(name + " terminated")
    }
  }


  /* raw stdout */

  private def stdout_actor(): (Thread, Actor) =
  {
    val name = "standard_output"
    Simple_Thread.actor(name) {
      var result = new StringBuilder(100)

      var finished = false
      while (!finished) {
        try {
          //{{{
          var c = -1
          var done = false
          while (!done && (result.length == 0 || process.stdout.ready)) {
            c = process.stdout.read
            if (c >= 0) result.append(c.asInstanceOf[Char])
            else done = true
          }
          if (result.length > 0) {
            put_result(Markup.STDOUT, result.toString)
            result.length = 0
          }
          else {
            process.stdout.close
            finished = true
          }
          //}}}
        }
        catch { case e: IOException => system_result(name + ": " + e.getMessage) }
      }
      system_result(name + " terminated")
    }
  }


  /* command input */

  private def input_actor(raw_stream: OutputStream): (Thread, Actor) =
  {
    val name = "command_input"
    Simple_Thread.actor(name) {
      val stream = new BufferedOutputStream(raw_stream)
      var finished = false
      while (!finished) {
        try {
          //{{{
          receive {
            case Input_Chunks(chunks) =>
              stream.write(Standard_System.string_bytes(
                  chunks.map(_.length).mkString("", ",", "\n")));
              chunks.foreach(stream.write(_));
              stream.flush
            case Close =>
              stream.close
              finished = true
            case bad => System.err.println(name + ": ignoring bad message " + bad)
          }
          //}}}
        }
        catch { case e: IOException => system_result(name + ": " + e.getMessage) }
      }
      system_result(name + " terminated")
    }
  }


  /* message output */

  private def message_actor(stream: InputStream): (Thread, Actor) =
  {
    class EOF extends Exception
    class Protocol_Error(msg: String) extends Exception(msg)

    val name = "message_output"
    Simple_Thread.actor(name) {
      val default_buffer = new Array[Byte](65536)
      var c = -1

      def read_chunk(decode: Boolean): XML.Body =
      {
        //{{{
        // chunk size
        var n = 0
        c = stream.read
        if (c == -1) throw new EOF
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
          if (m != -1) i += m
        } while (m != -1 && n > i)

        if (i != n) throw new Protocol_Error("bad message chunk content")

        if (decode)
          YXML.parse_body_failsafe(Standard_System.decode_chars(Symbol.decode, buf, 0, n))
        else List(XML.Text(Standard_System.decode_chars(s => s, buf, 0, n).toString))
        //}}}
      }

      do {
        try {
          val header = read_chunk(true)
          header match {
            case List(XML.Elem(Markup(name, props), Nil))
                if name.size == 1 && Kind.message_markup.isDefinedAt(name(0)) =>
              val kind = Kind.message_markup(name(0))
              val body = read_chunk(kind != Markup.RAW)
              put_result(kind, props, body)
            case _ =>
              read_chunk(false)
              throw new Protocol_Error("bad header: " + header.toString)
          }
        }
        catch {
          case e: IOException => system_result("Cannot read message:\n" + e.getMessage)
          case e: Protocol_Error => system_result("Malformed message:\n" + e.getMessage)
          case _: EOF =>
        }
      } while (c != -1)
      stream.close

      system_result(name + " terminated")
    }
  }


  /** main methods **/

  def input_raw(text: String): Unit = standard_input._2 ! Input_Text(text)

  def input_bytes(name: String, args: Array[Byte]*): Unit =
    command_input._2 ! Input_Chunks(Standard_System.string_bytes(name) :: args.toList)

  def input(name: String, args: String*): Unit =
  {
    receiver(new Input(name, args.toList))
    input_bytes(name, args.map(Standard_System.string_bytes): _*)
  }

  def close(): Unit = { close(command_input); close(standard_input) }
}
