/*  Title:      Pure/System/progress.scala
    Author:     Makarius

Progress context for system processes.
*/

package isabelle


import java.util.{Map => JMap}
import java.io.{File => JFile}


object Progress {
  object Kind extends Enumeration { val writeln, warning, error_message = Value }
  sealed case class Message(kind: Kind.Value, text: String) {
    def output_text: String =
      kind match {
        case Kind.writeln => Output.writeln_text(text)
        case Kind.warning => Output.warning_text(text)
        case Kind.error_message => Output.error_message_text(text)
      }

    override def toString: String = output_text
  }

  sealed case class Theory(theory: String, session: String = "", percentage: Option[Int] = None) {
    def message: Message =
      Message(Kind.writeln, print_session + print_theory + print_percentage)

    def print_session: String = if (session == "") "" else session + ": "
    def print_theory: String = "theory " + theory
    def print_percentage: String =
      percentage match { case None => "" case Some(p) => " " + p + "%" }
  }
}

class Progress {
  def echo(message: Progress.Message) = {}

  def echo(msg: String): Unit =
    echo(Progress.Message(Progress.Kind.writeln, msg))
  def echo_warning(msg: String): Unit =
    echo(Progress.Message(Progress.Kind.warning, msg))
  def echo_error_message(msg: String): Unit =
    echo(Progress.Message(Progress.Kind.error_message, msg))

  def echo_if(cond: Boolean, msg: String): Unit = if (cond) echo(msg)

  def verbose: Boolean = false
  def theory(theory: Progress.Theory): Unit = if (verbose) echo(theory.message)

  def nodes_status(nodes_status: Document_Status.Nodes_Status): Unit = {}

  def timeit[A](body: => A, message: Exn.Result[A] => String = null, enabled: Boolean = true): A =
    Timing.timeit(body, message = message, enabled = enabled, output = echo)

  @volatile protected var is_stopped = false
  def stop(): Unit = { is_stopped = true }
  def stopped: Boolean = {
    if (Thread.interrupted()) is_stopped = true
    is_stopped
  }

  def interrupt_handler[A](e: => A): A = POSIX_Interrupt.handler { stop() } { e }
  def expose_interrupt(): Unit = if (stopped) throw Exn.Interrupt()
  override def toString: String = if (stopped) "Progress(stopped)" else "Progress"

  def bash(script: String,
    cwd: JFile = null,
    env: JMap[String, String] = Isabelle_System.settings(),
    redirect: Boolean = false,
    echo: Boolean = false,
    watchdog: Time = Time.zero,
    strict: Boolean = true
  ): Process_Result = {
    val result =
      Isabelle_System.bash(script, cwd = cwd, env = env, redirect = redirect,
        progress_stdout = echo_if(echo, _),
        progress_stderr = echo_if(echo, _),
        watchdog = if (watchdog.is_zero) None else Some((watchdog, _ => stopped)),
        strict = strict)
    if (strict && stopped) throw Exn.Interrupt() else result
  }
}

class Console_Progress(override val verbose: Boolean = false, stderr: Boolean = false)
extends Progress {
  override def echo(message: Progress.Message): Unit =
    Output.output(message.output_text, stdout = !stderr, include_empty = true)
}

class File_Progress(path: Path, override val verbose: Boolean = false) extends Progress {
  override def echo(message: Progress.Message): Unit =
    File.append(path, message.output_text + "\n")

  override def toString: String = path.toString
}


/* structured program progress */

object Program_Progress {
  class Program private[Program_Progress](heading: String, title: String) {
    private val output_buffer = new StringBuffer(256)  // synchronized

    def echo(message: Progress.Message): Unit = synchronized {
      if (output_buffer.length() > 0) output_buffer.append('\n')
      output_buffer.append(message.output_text)
    }

    val start_time: Time = Time.now()
    private var stop_time: Option[Time] = None
    def stop_now(): Unit = synchronized { stop_time = Some(Time.now()) }

    def output(): (Command.Results, XML.Body) = synchronized {
      val output_text = output_buffer.toString
      val elapsed_time = stop_time.map(t => t - start_time)

      val message_prefix = heading + " "
      val message_suffix =
        elapsed_time match {
          case None => " ..."
          case Some(t) => " ... (" + t.message + " elapsed time)"
        }

      val (results, message) =
        if (output_text.isEmpty) {
          (Command.Results.empty, XML.string(message_prefix + title + message_suffix))
        }
        else {
          val i = Document_ID.make()
          val results = Command.Results.make(List(i -> Protocol.writeln_message(output_text)))
          val message =
            XML.string(message_prefix) :::
            List(XML.Elem(Markup(Markup.WRITELN, Markup.Serial(i)), XML.string(title))) :::
            XML.string(message_suffix)
          (results, message)
        }

      (results, List(XML.elem(Markup.TRACING_MESSAGE, message)))
    }
  }
}

abstract class Program_Progress(
  default_heading: String = "Running",
  default_title: String = "program",
  override val verbose: Boolean = false
) extends Progress {
  private var _finished_programs: List[Program_Progress.Program] = Nil
  private var _running_program: Option[Program_Progress.Program] = None

  def output(): (Command.Results, XML.Body) = synchronized {
    val programs = (_running_program.toList ::: _finished_programs).reverse
    val programs_output = programs.map(_.output())
    val results = Command.Results.merge(programs_output.map(_._1))
    val body = Library.separate(Pretty.Separator, programs_output.map(_._2)).flatten
    (results, body)
  }

  private def start_program(heading: String, title: String): Unit = synchronized {
    _running_program = Some(new Program_Progress.Program(heading, title))
  }

  def stop_program(): Unit = synchronized {
    _running_program match {
      case Some(program) =>
        program.stop_now()
        _finished_programs ::= program
        _running_program = None
      case None =>
    }
  }

  def detect_program(s: String): Option[String]

  override def echo(message: Progress.Message): Unit = synchronized {
    val writeln_msg = if (message.kind == Progress.Kind.writeln) message.text else ""
    detect_program(writeln_msg).map(Word.explode) match {
      case Some(a :: bs) =>
        stop_program()
        start_program(a, Word.implode(bs))
      case _ =>
        if (_running_program.isEmpty) start_program(default_heading, default_title)
        _running_program.get.echo(message)
    }
  }
}
