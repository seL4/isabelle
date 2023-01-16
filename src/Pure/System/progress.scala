/*  Title:      Pure/System/progress.scala
    Author:     Makarius

Progress context for system processes.
*/

package isabelle


import java.util.{Map => JMap}
import java.io.{File => JFile}


object Progress {
  sealed case class Theory(theory: String, session: String = "", percentage: Option[Int] = None) {
    def message: String = print_session + print_theory + print_percentage

    def print_session: String = if (session == "") "" else session + ": "
    def print_theory: String = "theory " + theory
    def print_percentage: String =
      percentage match { case None => "" case Some(p) => " " + p + "%" }
  }
}

class Progress {
  def echo(msg: String): Unit = {}
  def echo_if(cond: Boolean, msg: String): Unit = { if (cond) echo(msg) }
  def theory(theory: Progress.Theory): Unit = {}
  def nodes_status(nodes_status: Document_Status.Nodes_Status): Unit = {}

  def echo_warning(msg: String): Unit = echo(Output.warning_text(msg))
  def echo_error_message(msg: String): Unit = echo(Output.error_message_text(msg))

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

class Console_Progress(verbose: Boolean = false, stderr: Boolean = false) extends Progress {
  override def echo(msg: String): Unit =
    Output.writeln(msg, stdout = !stderr, include_empty = true)

  override def theory(theory: Progress.Theory): Unit =
    if (verbose) echo(theory.message)
}

class File_Progress(path: Path, verbose: Boolean = false) extends Progress {
  override def echo(msg: String): Unit =
    File.append(path, msg + "\n")

  override def theory(theory: Progress.Theory): Unit =
    if (verbose) echo(theory.message)

  override def toString: String = path.toString
}


/* structured program progress */

object Program_Progress {
  class Program private[Program_Progress](title: String) {
    private val output_buffer = new StringBuffer(256)  // synchronized

    def echo(msg: String): Unit = synchronized {
      if (output_buffer.length() > 0) output_buffer.append('\n')
      output_buffer.append(msg)
    }

    val start_time: Time = Time.now()
    private var stop_time: Option[Time] = None
    def stop_now(): Unit = synchronized { stop_time = Some(Time.now()) }

    def output(heading: String): (Command.Results, XML.Body) = synchronized {
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

abstract class Program_Progress extends Progress {
  private var _finished_programs: List[Program_Progress.Program] = Nil
  private var _running_program: Option[Program_Progress.Program] = None

  def output(heading: String = "Running"): (Command.Results, XML.Body) = synchronized {
    val programs = (_running_program.toList ::: _finished_programs).reverse
    val programs_output = programs.map(_.output(heading))
    val results = Command.Results.merge(programs_output.map(_._1))
    val body = Library.separate(Pretty.Separator, programs_output.map(_._2)).flatten
    (results, body)
  }

  private def start_program(title: String): Unit = synchronized {
    _running_program = Some(new Program_Progress.Program(title))
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

  override def echo(msg: String): Unit = synchronized {
    detect_program(msg) match {
      case Some(title) =>
        stop_program()
        start_program(title)
      case None =>
        if (_running_program.isEmpty) start_program("program")
        _running_program.get.echo(msg)
    }
  }
}
