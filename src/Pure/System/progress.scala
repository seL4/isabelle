/*  Title:      Pure/System/progress.scala
    Author:     Makarius

Progress context for system processes.
*/

package isabelle


import java.util.{Map => JMap}


object Progress {
  /* output */

  sealed abstract class Output { def message: Message }

  enum Kind { case writeln, warning, error_message }
  sealed case class Message(
    kind: Kind,
    text: String,
    verbose: Boolean = false
  ) extends Output {
    override def message: Message = this

    def output_text: String =
      kind match {
        case Kind.writeln => Output.writeln_text(text)
        case Kind.warning => Output.warning_text(text)
        case Kind.error_message => Output.error_message_text(text)
      }

    override def toString: String = output_text
  }

  sealed case class Theory(
    theory: String,
    session: String = "",
    percentage: Option[Int] = None,
    total_time: Time = Time.zero
  ) extends Output {
    def message: Message =
      Message(Kind.writeln, print_session + print_theory + print_percentage + print_total_time,
        verbose = true)

    def print_session: String = if_proper(session, session + ": ")
    def print_theory: String = "theory " + theory
    def print_percentage: String =
      percentage match { case None => "" case Some(p) => " " + p + "%" }
    def print_total_time: String =
      if (total_time.is_relevant) " (" + total_time.message + " elapsed time)" else ""
  }

  sealed case class Nodes_Status(
    domain: List[Document.Node.Name],
    document_status: Document_Status.Nodes_Status,
    session: String = "",
    old: Option[Document_Status.Nodes_Status] = None
  ) {
    def message: Message =
      Message(Kind.writeln, cat_lines(domain.map(name => theory(name).message.text)),
        verbose = true)

    def apply(name: Document.Node.Name): Document_Status.Node_Status =
      document_status(name)

    def theory(name: Document.Node.Name): Theory = {
      val node_status = apply(name)
      Theory(theory = name.theory, session = session, total_time = node_status.total_timing.elapsed)
    }
  }
}

class Progress {
  def now(): Date = Date.now()
  val start: Date = now()

  def verbose: Boolean = false
  final def do_output(message: Progress.Message): Boolean = !message.verbose || verbose

  def output(message: Progress.Message): Unit = {}

  final def echo(msg: String, verbose: Boolean = false): Unit =
    output(Progress.Message(Progress.Kind.writeln, msg, verbose = verbose))
  final def echo_warning(msg: String, verbose: Boolean = false): Unit =
    output(Progress.Message(Progress.Kind.warning, msg, verbose = verbose))
  final def echo_error_message(msg: String, verbose: Boolean = false): Unit =
    output(Progress.Message(Progress.Kind.error_message, msg, verbose = verbose))

  final def echo_if(cond: Boolean, msg: String): Unit = if (cond) echo(msg)

  def theory(theory: Progress.Theory): Unit = output(theory.message)
  def nodes_status(nodes_status: Progress.Nodes_Status): Unit = {}

  final def capture[A](e: => A, msg: String, err: Throwable => String): Exn.Result[A] = {
    echo(msg)
    try { Exn.Res(e) }
    catch { case exn: Throwable => echo_error_message(err(exn)); Exn.Exn[A](exn) }
  }

  final def timeit[A](
    body: => A,
    message: Exn.Result[A] => String = null,
    enabled: Boolean = true
  ): A = Timing.timeit(body, message = message, enabled = enabled, output = echo(_))

  @volatile private var is_stopped = false
  def stop(): Unit = { is_stopped = true }
  def stopped: Boolean = {
    if (Thread.interrupted()) is_stopped = true
    is_stopped
  }

  final def interrupt_handler[A](e: => A): A = POSIX_Interrupt.handler { stop() } { e }
  final def expose_interrupt(): Unit = if (stopped) throw Exn.Interrupt()
  override def toString: String = if (stopped) "Progress(stopped)" else "Progress"

  final def bash(script: String,
    ssh: SSH.System = SSH.Local,
    cwd: Path = Path.current,
    env: JMap[String, String] = Isabelle_System.Settings.env(),  // ignored for remote ssh
    redirect: Boolean = false,
    echo: Boolean = false,
    watchdog_time: Time = Time.zero,
    strict: Boolean = true
  ): Process_Result = {
    val result =
      Isabelle_System.bash(script, ssh = ssh, cwd = cwd, env = env, redirect = redirect,
        progress_stdout = echo_if(echo, _),
        progress_stderr = echo_if(echo, _),
        watchdog = Bash.Watchdog(watchdog_time, _ => stopped),
        strict = strict)
    if (strict && stopped) throw Exn.Interrupt() else result
  }
}

class Console_Progress(override val verbose: Boolean = false, stderr: Boolean = false)
extends Progress {
  override def output(message: Progress.Message): Unit = synchronized {
    if (do_output(message)) {
      Output.output(message.output_text, stdout = !stderr, include_empty = true)
    }
  }

  override def toString: String = super.toString + ": console"
}

class File_Progress(path: Path, override val verbose: Boolean = false)
extends Progress {
  override def output(message: Progress.Message): Unit = synchronized {
    if (do_output(message)) File.append(path, message.output_text + "\n")
  }

  override def toString: String = super.toString + ": " + path.toString
}
