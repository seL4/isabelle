/*  Title:      Pure/System/progress.scala
    Author:     Makarius

Progress context for system processes.
*/

package isabelle


import java.util.{Map => JMap}
import scala.collection.mutable


object Progress {
  /* output */

  sealed abstract class Msg {
    def verbose: Boolean
    def status: Boolean
    def message: Message
  }

  type Output = List[Msg]
  type Session_Output = List[(String, Msg)]

  def output_theory(msg: Msg): Msg =
    msg match {
      case thy: Theory if thy.verbose => thy.copy(verbose = false)
      case _ => msg
    }

  enum Kind { case writeln, warning, error_message }
  sealed case class Message(
    kind: Kind,
    text: String,
    override val verbose: Boolean = false,
    override val status: Boolean = false
  ) extends Msg {
    override def message: Message = this

    lazy val output_text: String =
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
    cumulated_time: Time = Time.zero,
    override val verbose: Boolean = true,
    override val status: Boolean = false
  ) extends Msg {
    override def message: Message =
      Message(Kind.writeln, print_session + print_theory + print_percentage + print_cumulated_time,
        verbose = verbose, status = status)

    def print_session: String = if_proper(session, session + ": ")
    def print_theory: String = "theory " + theory
    def print_percentage: String =
      percentage match { case None => "" case Some(p) => " " + p + "%" }
    def print_cumulated_time: String =
      if (cumulated_time.is_relevant) " (" + cumulated_time.message + " cumulated time)" else ""
  }

  object Nodes_Status {
    def empty(session: String): Nodes_Status =
      Nodes_Status(Date.now(), Nil, Document_Status.Nodes_Status.empty, session = session)
  }

  sealed case class Nodes_Status(
    now: Date,
    domain: List[Document.Node.Name],
    document_status: Document_Status.Nodes_Status,
    session: String = "",
    old: Option[Document_Status.Nodes_Status] = None
  ) {
    def apply(name: Document.Node.Name): Document_Status.Node_Status =
      document_status(name)

    def theory(
      name: Document.Node.Name,
      node_status: Document_Status.Node_Status,
      status: Boolean = false): Theory =
      Theory(theory = name.theory, session = session,
        percentage = Some(node_status.percentage),
        cumulated_time = node_status.cumulated_time,
        status = status)

    def old_percentage(name: Document.Node.Name): Int =
      if (old.isEmpty) 0 else old.get(name).percentage

    def completed_theories: List[Theory] =
      domain.flatMap({ name =>
        val st = apply(name)
        val p = st.percentage
        if (p == 100 && p != old_percentage(name)) Some(theory(name, st)) else None
      })

    def status_theories: List[Theory] =
      domain.flatMap({ name =>
        val st = apply(name)
        val p = st.percentage
        if (st.progress || (p < 100 && p != old_percentage(name))) {
          Some(theory(name, st, status = true))
        }
        else None
      })

    def long_running_commands(threshold: Time, status: Boolean = false): List[Progress.Message] =
      List.from(
        for {
          name <- domain.iterator
          st = apply(name)
          command_timings <- st.command_timings.valuesIterator
          run <- command_timings.long_running(now, threshold).iterator
        } yield {
          val text =
            if_proper(session, session + ": ") +
              "command " + quote(run.name) + " running for " + run.time(now).message +
              " (line " + run.line + " of theory " + quote(name.theory) + ")"
          Progress.Message(Progress.Kind.writeln, text, verbose = true, status = status)
        })
  }


  /* status lines (e.g. at bottom of output) */

  trait Status extends Progress {
    def status_threshold: Time = Time.zero
    def status_detailed: Boolean = false

    def status_output(msgs: Progress.Output): Unit

    def status_hide(msgs: Progress.Output): Unit = ()

    protected var _status: Progress.Session_Output = Nil

    def status_clear(): Progress.Session_Output = synchronized {
      val status = _status
      _status = Nil
      status_hide(status.map(_._2))
      status
    }

    private def output_status(status: Progress.Session_Output): Unit = synchronized {
      _status = Nil
      status_output(status.map(_._2))
      _status = status
    }

    override def output(msgs: Progress.Output): Unit = synchronized {
      if (msgs.nonEmpty) {
        val status = status_clear()
        status_output(msgs)
        output_status(status)
      }
    }

    override def nodes_status(nodes_status: Progress.Nodes_Status): Unit = synchronized {
      val long_running_commands =
        nodes_status.long_running_commands(status_threshold, status = status_detailed)
      val output_commands = if (status_detailed) Nil else long_running_commands

      val old_status = status_clear()
      val new_status = {
        val buf = new mutable.ListBuffer[(String, Progress.Msg)]
        val session = nodes_status.session
        for (old <- old_status if old._1 < session) buf += old
        if (status_detailed) {
          for (thy <- nodes_status.status_theories) buf += (session -> thy)
          for (msg <- long_running_commands) buf += (session -> msg)
        }
        for (old <- old_status if old._1 > session) buf += old
        buf.toList
      }

      output(nodes_status.completed_theories ::: output_commands)
      output_status(new_status)
    }
  }
}

class Progress {
  def now(): Date = Date.now()
  val start: Date = now()

  def verbose: Boolean = false
  final def do_output(msg: Progress.Msg): Boolean = !msg.verbose || verbose

  def output(msgs: Progress.Output): Unit = {}

  final def output_text(msgs: Progress.Output, terminate: Boolean = false): String = {
    val lines = msgs.flatMap(msg => if (do_output(msg)) Some(msg.message.output_text) else None)
    if (terminate) Library.terminate_lines(lines) else cat_lines(lines)
  }

  final def echo(msg: String, verbose: Boolean = false): Unit =
    output(List(Progress.Message(Progress.Kind.writeln, msg, verbose = verbose)))
  final def echo_warning(msg: String, verbose: Boolean = false): Unit =
    output(List(Progress.Message(Progress.Kind.warning, msg, verbose = verbose)))
  final def echo_error_message(msg: String, verbose: Boolean = false): Unit =
    output(List(Progress.Message(Progress.Kind.error_message, msg, verbose = verbose)))

  final def echo_if(cond: Boolean, msg: String): Unit = if (cond) echo(msg)

  final def theory(theory: Progress.Theory): Unit = output(List(theory))

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
  def stopped: Boolean = is_stopped

  def interrupt_handler[A](e: => A): A =
    Isabelle_Thread.interrupt_handle(stop(), permissive = true) { e }

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

class Console_Progress(
  override val verbose: Boolean = false,
  threshold: Time = Build.progress_threshold(Options.defaults),
  detailed: Boolean = false,
  stderr: Boolean = false)
extends Progress with Progress.Status {
  override def interrupt_handler[A](e: => A): A =
    Exn.Interrupt.signal_handler(stop()) { super.interrupt_handler(e) }

  override def status_threshold: Time = threshold
  override def status_detailed: Boolean = detailed

  override def status_hide(msgs: Progress.Output): Unit = synchronized {
    val txt = output_text(msgs, terminate = true)
    Output.delete_lines(Library.count_newlines(txt), stdout = !stderr)
  }

  override def status_output(msgs: Progress.Output): Unit = synchronized {
    for (msg <- msgs if do_output(msg)) {
      val txt0 = msg.message.output_text
      val txt1 = if (msg.status) "\u001b[7m" + txt0 + "\u001b[0m" else txt0
      Output.output(txt1, stdout = !stderr, include_empty = true)
    }
  }

  override def toString: String = super.toString + ": console"
}

class File_Progress(path: Path, override val verbose: Boolean = false)
extends Progress with Progress.Status {
  override def status_output(msgs: Progress.Output): Unit = synchronized {
    val txt = output_text(msgs, terminate = true)
    if (txt.nonEmpty) File.append(path, txt)
  }

  override def toString: String = super.toString + ": " + path.toString
}
