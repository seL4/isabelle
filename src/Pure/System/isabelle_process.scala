/*  Title:      Pure/System/isabelle_process.scala
    Author:     Makarius
    Options:    :folding=explicit:collapseFolds=1:

Isabelle process management -- always reactive due to multi-threaded I/O.
*/

package isabelle


import java.util.concurrent.LinkedBlockingQueue
import java.io.{BufferedReader, BufferedWriter, InputStreamReader, OutputStreamWriter,
  InputStream, OutputStream, BufferedOutputStream, IOException}

import scala.actors.Actor
import Actor._


object Isabelle_Process
{
  /* messages */

  sealed abstract class Message

  class Input(name: String, args: List[String]) extends Message
  {
    override def toString: String =
      XML.Elem(Markup(Markup.PROVER_COMMAND, List((Markup.NAME, name))),
        args.map(s =>
          List(XML.Text("\n"), XML.elem(Markup.PROVER_ARG, YXML.parse_body(s)))).flatten).toString
  }

  class Output(val message: XML.Elem) extends Message
  {
    def kind: String = message.markup.name
    def properties: Properties.T = message.markup.properties
    def body: XML.Body = message.body

    def is_init = kind == Markup.INIT
    def is_exit = kind == Markup.EXIT
    def is_stdout = kind == Markup.STDOUT
    def is_stderr = kind == Markup.STDERR
    def is_system = kind == Markup.SYSTEM
    def is_status = kind == Markup.STATUS
    def is_report = kind == Markup.REPORT
    def is_syslog = is_init || is_exit || is_system || is_stderr

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
  }

  class Protocol_Output(props: Properties.T, val bytes: Bytes)
    extends Output(XML.Elem(Markup(Markup.PROTOCOL, props), Nil))
  {
    lazy val text: String = bytes.toString
  }
}


class Isabelle_Process(
    receiver: Isabelle_Process.Message => Unit = Console.println(_),
    arguments: List[String] = Nil)
{
  import Isabelle_Process._


  /* text representation */

  def encode(s: String): String = Symbol.encode(s)
  def decode(s: String): String = Symbol.decode(s)

  object Encode
  {
    val string: XML.Encode.T[String] = (s => XML.Encode.string(encode(s)))
  }


  /* output */

  val xml_cache = new XML.Cache()

  private def system_output(text: String)
  {
    receiver(new Output(XML.Elem(Markup(Markup.SYSTEM, Nil), List(XML.Text(text)))))
  }

  private def protocol_output(props: Properties.T, bytes: Bytes)
  {
    receiver(new Protocol_Output(props, bytes))
  }

  private def output(kind: String, props: Properties.T, body: XML.Body)
  {
    if (kind == Markup.INIT) system_channel.accepted()

    val main = XML.Elem(Markup(kind, props), Protocol.clean_message(body))
    val reports = Protocol.message_reports(props, body)
    for (msg <- main :: reports) receiver(new Output(xml_cache.elem(msg)))
  }

  private def exit_message(rc: Int)
  {
    output(Markup.EXIT, Markup.Return_Code(rc), List(XML.Text("Return code: " + rc.toString)))
  }


  /* command input actor */

  private case class Input_Chunks(chunks: List[Bytes])

  private case object Close
  private def close(p: (Thread, Actor))
  {
    if (p != null && p._1.isAlive) {
      p._2 ! Close
      p._1.join
    }
  }

  @volatile private var command_input: (Thread, Actor) = null


  /** process manager **/

  def command_line(channel: System_Channel, args: List[String]): List[String] =
    Isabelle_System.getenv_strict("ISABELLE_PROCESS") :: (channel.isabelle_args ::: args)

  private val system_channel = System_Channel()

  private val process =
    try {
      val cmdline = command_line(system_channel, arguments)
      new Isabelle_System.Managed_Process(null, null, false, cmdline: _*)
    }
    catch { case e: IOException => system_channel.accepted(); throw(e) }

  val (_, process_result) =
    Simple_Thread.future("process_result") { process.join }

  private def terminate_process()
  {
    try { process.terminate }
    catch { case e: IOException => system_output("Failed to terminate Isabelle: " + e.getMessage) }
  }

  private val process_manager = Simple_Thread.fork("process_manager")
  {
    val (startup_failed, startup_errors) =
    {
      var finished: Option[Boolean] = None
      val result = new StringBuilder(100)
      while (finished.isEmpty && (process.stderr.ready || !process_result.is_finished)) {
        while (finished.isEmpty && process.stderr.ready) {
          try {
            val c = process.stderr.read
            if (c == 2) finished = Some(true)
            else result += c.toChar
          }
          catch { case _: IOException => finished = Some(false) }
        }
        Thread.sleep(10)
      }
      (finished.isEmpty || !finished.get, result.toString.trim)
    }
    if (startup_errors != "") system_output(startup_errors)

    process.stdin.close
    if (startup_failed) {
      exit_message(127)
      Thread.sleep(300)
      terminate_process()
      process_result.join
    }
    else {
      val (command_stream, message_stream) = system_channel.rendezvous()

      val stdout = physical_output_actor(false)
      val stderr = physical_output_actor(true)
      command_input = input_actor(command_stream)
      val message = message_actor(message_stream)

      val rc = process_result.join
      system_output("process terminated")
      close(command_input)
      for ((thread, _) <- List(stdout, stderr, command_input, message))
        thread.join
      system_output("process_manager terminated")
      exit_message(rc)
    }
    system_channel.accepted()
  }


  /* management methods */

  def join() { process_manager.join() }

  def terminate()
  {
    close(command_input)
    system_output("Terminating Isabelle process")
    terminate_process()
  }



  /** stream actors **/

  /* physical output */

  private def physical_output_actor(err: Boolean): (Thread, Actor) =
  {
    val (name, reader, markup) =
      if (err) ("standard_error", process.stderr, Markup.STDERR)
      else ("standard_output", process.stdout, Markup.STDOUT)

    Simple_Thread.actor(name) {
      try {
        var result = new StringBuilder(100)
        var finished = false
        while (!finished) {
          //{{{
          var c = -1
          var done = false
          while (!done && (result.length == 0 || reader.ready)) {
            c = reader.read
            if (c >= 0) result.append(c.asInstanceOf[Char])
            else done = true
          }
          if (result.length > 0) {
            output(markup, Nil, List(XML.Text(decode(result.toString))))
            result.length = 0
          }
          else {
            reader.close
            finished = true
          }
          //}}}
        }
      }
      catch { case e: IOException => system_output(name + ": " + e.getMessage) }
      system_output(name + " terminated")
    }
  }


  /* command input */

  private def input_actor(raw_stream: OutputStream): (Thread, Actor) =
  {
    val name = "command_input"
    Simple_Thread.actor(name) {
      try {
        val stream = new BufferedOutputStream(raw_stream)
        var finished = false
        while (!finished) {
          //{{{
          receive {
            case Input_Chunks(chunks) =>
              Bytes(chunks.map(_.length).mkString("", ",", "\n")).write(stream)
              chunks.foreach(_.write(stream))
              stream.flush
            case Close =>
              stream.close
              finished = true
            case bad => System.err.println(name + ": ignoring bad message " + bad)
          }
          //}}}
        }
      }
      catch { case e: IOException => system_output(name + ": " + e.getMessage) }
      system_output(name + " terminated")
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

      def read_int(): Int =
      //{{{
      {
        var n = 0
        c = stream.read
        if (c == -1) throw new EOF
        while (48 <= c && c <= 57) {
          n = 10 * n + (c - 48)
          c = stream.read
        }
        if (c != 10)
          throw new Protocol_Error("malformed header: expected integer followed by newline")
        else n
      }
      //}}}

      def read_chunk_bytes(): (Array[Byte], Int) =
      //{{{
      {
        val n = read_int()
        val buf =
          if (n <= default_buffer.size) default_buffer
          else new Array[Byte](n)

        var i = 0
        var m = 0
        do {
          m = stream.read(buf, i, n - i)
          if (m != -1) i += m
        }
        while (m != -1 && n > i)

        if (i != n)
          throw new Protocol_Error("bad chunk (unexpected EOF after " + i + " of " + n + " bytes)")

        (buf, n)
      }
      //}}}

      def read_chunk(): XML.Body =
      {
        val (buf, n) = read_chunk_bytes()
        YXML.parse_body_failsafe(UTF8.decode_chars(decode, buf, 0, n))
      }

      try {
        do {
          try {
            val header = read_chunk()
            header match {
              case List(XML.Elem(Markup(name, props), Nil)) =>
                val kind = name.intern
                if (kind == Markup.PROTOCOL) {
                  val (buf, n) = read_chunk_bytes()
                  protocol_output(props, Bytes(buf, 0, n))
                }
                else {
                  val body = read_chunk()
                  output(kind, props, body)
                }
              case _ =>
                read_chunk()
                throw new Protocol_Error("bad header: " + header.toString)
            }
          }
          catch { case _: EOF => }
        }
        while (c != -1)
      }
      catch {
        case e: IOException => system_output("Cannot read message:\n" + e.getMessage)
        case e: Protocol_Error => system_output("Malformed message:\n" + e.getMessage)
      }
      stream.close

      system_output(name + " terminated")
    }
  }


  /** main methods **/

  def protocol_command_raw(name: String, args: Bytes*): Unit =
    command_input._2 ! Input_Chunks(Bytes(name) :: args.toList)

  def protocol_command(name: String, args: String*)
  {
    receiver(new Input(name, args.toList))
    protocol_command_raw(name, args.map(Bytes(_)): _*)
  }

  def options(opts: Options): Unit =
    protocol_command("Isabelle_Process.options", YXML.string_of_body(opts.encode))
}
