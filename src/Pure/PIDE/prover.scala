/*  Title:      Pure/PIDE/prover.scala
    Author:     Makarius
    Options:    :folding=explicit:

Prover process wrapping.
*/

package isabelle


import java.io.{InputStream, OutputStream, BufferedOutputStream, IOException}
import java.nio.channels.ClosedChannelException


object Prover {
  /* messages */

  sealed abstract class Message
  type Receiver = Message => Unit

  class Input(val name: String, val args: List[XML.Body]) extends Message {
    override def toString: String =
      XML.Elem(Markup(Markup.PROVER_COMMAND, List((Markup.NAME, name))),
        args.flatMap(arg => List(XML.newline, XML.elem(Markup.PROVER_ARG, arg)))).toString
  }

  class Output(val message: XML.Elem) extends Message {
    def kind: String = message.markup.name
    def properties: Properties.T = message.markup.properties
    def body: XML.Body = message.body

    def is_init: Boolean = kind == Markup.INIT
    def is_exit: Boolean = kind == Markup.EXIT
    def is_stdout: Boolean = kind == Markup.STDOUT
    def is_stderr: Boolean = kind == Markup.STDERR
    def is_system: Boolean = kind == Markup.SYSTEM
    def is_status: Boolean = kind == Markup.STATUS
    def is_report: Boolean = kind == Markup.REPORT

    override def toString: String = {
      val res =
        if (is_status || is_report) message.body.map(_.toString).mkString
        else Pretty.string_of(message.body, metric = Symbol.Metric)
      if (properties.isEmpty)
        kind + " [[" + res + "]]"
      else
        kind + " " +
          (properties.map(Properties.Eq.apply)).mkString("{", ",", "}") + " [[" + res + "]]"
    }
  }

  class Malformed(msg: String) extends Exn.User_Error("Malformed prover message: " + msg)
  def bad_header(print: String): Nothing = throw new Malformed("bad message header\n" + print)
  def bad_chunks(): Nothing = throw new Malformed("bad message chunks")

  def the_chunk(chunks: List[Bytes], print: => String): Bytes =
    chunks match {
      case List(chunk) => chunk
      case _ => throw new Malformed("single chunk expected: " + print)
    }

  class System_Output(text: String) extends
    Output(XML.Elem(Markup(Markup.SYSTEM, Nil), List(XML.Text(text))))

  class Protocol_Output(props: Properties.T, val chunks: List[Bytes])
  extends Output(XML.elem(Markup(Markup.PROTOCOL, props))) {
    def chunk: Bytes = the_chunk(chunks, toString)
    lazy val text: String = chunk.text
  }
}


class Prover(
  receiver: Prover.Receiver,
  cache: XML.Cache,
  channel: System_Channel,
  process: Bash.Process,
  default_options: Options,
  log: Logger
) extends Protocol {
  /** options **/

  private var current_options = default_options

  def update_options(new_options: Options): Unit = synchronized {
    val update =
      for (ch <- new_options.changed(defaults = current_options) if !ch.unknown)
        yield ch.name -> ch.value
    if (update.nonEmpty) {
      protocol_command("Prover.update_options",
        { import XML.Encode._; list(pair(string, string))(update) })
      current_options = new_options
    }
  }

  def options: Options = synchronized { current_options }

  def verbose: Boolean = options.bool("pide_prover_verbose")



  /** receiver output **/

  private def protocol_message(props: Properties.T, chunks: List[Bytes]): Unit =
    receiver(new Prover.Protocol_Output(props, chunks))

  private def output(kind: String, props: Properties.T, body: XML.Body): Unit = {
    val main = XML.Elem(Markup(kind, props), Protocol_Message.clean_reports(body))
    val reports = Protocol_Message.reports(props, body)
    for (msg <- main :: reports) receiver(new Prover.Output(cache.elem(msg)))
  }

  private def exit_message(result: Process_Result): Unit = {
    output(Markup.EXIT, Markup.Process_Result.make(result),
      List(XML.Text(result.print_return_code)))
  }



  /** process manager **/

  private val process_result: Future[Process_Result] =
    Future.thread("process_result") {
      val rc = process.join()
      val timing = process.get_timing
      Process_Result(rc, timing = timing)
    }

  private def terminate_process(): Unit = {
    try { process.terminate() }
    catch { case ERROR(msg) => log.error_message("Failed to terminate prover process: " + msg) }
  }

  private val process_manager = Isabelle_Thread.fork(name = "process_manager") {
    val stdout = physical_output(false)

    val (startup_failed, startup_errors) = {
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
        Time.seconds(0.05).sleep()
      }
      (finished.isEmpty || !finished.get, Library.trim_string(result.toString))
    }
    if (startup_errors.nonEmpty) log.error_message(startup_errors)

    if (startup_failed) {
      terminate_process()
      process_result.join
      stdout.join
      exit_message(Process_Result.startup_failure)
    }
    else {
      process.stdin.write(channel.address + " " + channel.password)
      process.stdin.flush()
      process.stdin.close()
      val (command_stream, message_stream) = channel.rendezvous()

      command_input_init(command_stream)
      val stderr = physical_output(true)
      val message = message_output(message_stream)

      val result = process_result.join
      if (verbose) log("Prover process terminated")
      command_input_close()
      for (thread <- List(stdout, stderr, message)) thread.join()
      if (verbose) log("Prover process_manager terminated")
      exit_message(result)
    }
    channel.shutdown()
  }


  /* management methods */

  def join(): Unit = process_manager.join()

  def terminate(): Unit = {
    if (verbose) log("Prover process terminating ...")
    command_input_close()

    var count = 10
    while (!process_result.is_finished && count > 0) {
      Time.seconds(0.1).sleep()
      count -= 1
    }
    if (!process_result.is_finished) terminate_process()
  }



  /** process streams **/

  /* command input */

  private var command_input: Option[Consumer_Thread[List[Bytes]]] = None

  private def command_input_close(): Unit = command_input.foreach(_.shutdown())

  private def command_input_init(raw_stream: OutputStream): Unit = {
    val name = "command_input"
    val stream = new BufferedOutputStream(raw_stream)
    command_input =
      Some(
        Consumer_Thread.fork(name,
          { chunks =>
            try {
              Bytes(chunks.map(_.size).mkString("", ",", "\n")).write_stream(stream)
              chunks.foreach(_.write_stream(stream))
              stream.flush
              true
            }
            catch {
              case e: IOException =>
                log.error_message("Prover " + name + ": " + Exn.message(e))
                false
            }
          },
          finish = { () =>
            stream.close()
            if (verbose) log("Prover " + name + " terminated")
          }
        )
      )
  }


  /* physical output */

  private def physical_output(err: Boolean): Thread = {
    val (name, reader, markup) =
      if (err) ("standard_error", process.stderr, Markup.STDERR)
      else ("standard_output", process.stdout, Markup.STDOUT)

    Isabelle_Thread.fork(name = name) {
      try {
        val result = new StringBuilder(100)
        var finished = false
        while (!finished) {
          //{{{
          var c = -1
          var done = false
          while (!done && (result.isEmpty || reader.ready)) {
            c = reader.read
            if (c >= 0) result.append(c.asInstanceOf[Char])
            else done = true
          }
          if (result.nonEmpty) {
            output(markup, Nil, List(XML.Text(Symbol.decode(result.toString))))
            result.clear()
          }
          else {
            reader.close()
            finished = true
          }
          //}}}
        }
      }
      catch { case e: IOException => log.error_message("Prover " + name + ": " + Exn.message(e)) }
      if (verbose) log("Prover " + name + " terminated")
    }
  }


  /* message output */

  private def message_output(stream: InputStream): Thread = {
    def decode_prop(bytes: Bytes): Properties.Entry = {
      val (a, b) = Properties.Eq.parse(bytes.text)
      (Symbol.decode(a), Symbol.decode(b))
    }

    val thread_name = "message_output"
    Isabelle_Thread.fork(name = thread_name) {
      try {
        var finished = false
        while (!finished) {
          Byte_Message.read_message(stream) match {
            case None => finished = true
            case Some(k :: Value.Nat(props_length) :: rest) =>
              val kind = k.text
              val props = rest.take(props_length).map(decode_prop)
              val chunks = rest.drop(props_length)
              if (kind == Markup.PROTOCOL) protocol_message(props, chunks)
              else {
                val body = chunks.flatMap(Symbol.decode_yxml(_, cache = cache, failsafe = true))
                output(kind, props, body)
              }
            case Some(_) => Prover.bad_chunks()
          }
        }
      }
      catch {
        case _: ClosedChannelException =>
        case e: IOException => log.error_message("Failed to read prover message: " + Exn.message(e))
        case e: Prover.Malformed => log.error_message(Exn.message(e))
      }
      stream.close()

      if (verbose) log("Prover " + thread_name + " terminated")
    }
  }



  /** protocol commands **/

  def protocol_command_raw(name: String, args: List[Bytes]): Unit =
    command_input match {
      case Some(thread) if thread.is_active() =>
        if (verbose) {
          val payload = args.foldLeft(0L) { case (n, b) => n + b.size }
          log("protocol_command " + name + ", args = " + args.length + ", payload = " + payload)
        }
        thread.send(Bytes(name) :: args)
      case _ => error("Inactive prover input thread for command " + quote(name))
    }

  def protocol_command_args(name: String, args: List[XML.Body]): Unit = {
    receiver(new Prover.Input(name, args))
    protocol_command_raw(name, args.map(arg => Bytes(Symbol.encode_yxml(arg))))
  }

  def protocol_command(name: String, args: XML.Body*): Unit =
    protocol_command_args(name, args.toList)
}
