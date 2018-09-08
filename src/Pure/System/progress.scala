/*  Title:      Pure/System/progress.scala
    Author:     Makarius

Progress context for system processes.
*/

package isabelle


import java.io.{File => JFile}


object Progress
{
  def theory_message(session: String, theory: String): String =
    if (session == "") "theory " + theory else session + ": theory " + theory

  def theory_percentage_message(session: String, theory: String, percentage: Int): String =
    theory_message(session, theory) + ": " + percentage + "%"
}

class Progress
{
  def echo(msg: String) {}
  def echo_if(cond: Boolean, msg: String) { if (cond) echo(msg) }
  def theory(session: String, theory: String) {}
  def theory_percentage(session: String, theory: String, percentage: Int) {}
  def nodes_status(nodes_status: Document_Status.Nodes_Status) {}

  def echo_warning(msg: String) { echo(Output.warning_text(msg)) }
  def echo_error_message(msg: String) { echo(Output.error_message_text(msg)) }

  def timeit[A](message: String = "", enabled: Boolean = true)(e: => A): A =
    Timing.timeit(message, enabled, echo(_))(e)

  def stopped: Boolean = false
  def interrupt_handler[A](e: => A): A = e
  def expose_interrupt() { if (stopped) throw Exn.Interrupt() }
  override def toString: String = if (stopped) "Progress(stopped)" else "Progress"

  def bash(script: String,
    cwd: JFile = null,
    env: Map[String, String] = Isabelle_System.settings(),
    redirect: Boolean = false,
    echo: Boolean = false,
    strict: Boolean = true): Process_Result =
  {
    Isabelle_System.bash(script, cwd = cwd, env = env, redirect = redirect,
      progress_stdout = echo_if(echo, _),
      progress_stderr = echo_if(echo, _),
      strict = strict)
  }
}

object No_Progress extends Progress

class Console_Progress(verbose: Boolean = false, stderr: Boolean = false) extends Progress
{
  override def echo(msg: String): Unit =
    Output.writeln(msg, stdout = !stderr)

  override def theory(session: String, theory: String): Unit =
    if (verbose) echo(Progress.theory_message(session, theory))

  override def theory_percentage(session: String, theory: String, percentage: Int): Unit =
    if (verbose) echo(Progress.theory_percentage_message(session, theory, percentage))

  @volatile private var is_stopped = false
  override def interrupt_handler[A](e: => A): A =
    POSIX_Interrupt.handler { is_stopped = true } { e }
  override def stopped: Boolean =
  {
    if (Thread.interrupted) is_stopped = true
    is_stopped
  }
}

class File_Progress(path: Path, verbose: Boolean = false) extends Progress
{
  override def echo(msg: String): Unit =
    File.append(path, msg + "\n")

  override def theory(session: String, theory: String): Unit =
    if (verbose) echo(Progress.theory_message(session, theory))

  override def theory_percentage(session: String, theory: String, percentage: Int): Unit =
    if (verbose) echo(Progress.theory_percentage_message(session, theory, percentage))

  override def toString: String = path.toString
}
