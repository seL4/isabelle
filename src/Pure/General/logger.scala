/*  Title:      Pure/General/logger.scala
    Author:     Makarius

Minimal logging support.
*/

package isabelle


object Logger {
  def make_file(log_file: Option[Path], guard_time: Time = Time.min): Logger =
    log_file match {
      case Some(file) => new File_Logger(file, guard_time)
      case None => new Logger
    }

  def make_progress(progress: => Progress, guard_time: Time = Time.min): Logger = {
    val t = guard_time
    new Logger {
      override def toString: String = progress.toString
      override val guard_time: Time = t
      override def output(kind: Output.Kind, msg: => String): Unit =
        progress.output(List(Progress.Message(kind, msg)))
    }
  }

  def make_system_log(progress: => Progress, options: Options, guard_time: Time = Time.min): Logger =
    options.string("system_log") match {
      case "" => new Logger
      case "-" => make_progress(progress, guard_time = guard_time)
      case log_file => make_file(Some(Path.explode(log_file)), guard_time = guard_time)
    }
}

class Logger {
  val guard_time: Time = Time.min
  def guard(t: Time): Boolean = t >= guard_time
  def output(kind: Output.Kind, msg: => String): Unit = {}

  final def apply(
    msg: => String,
    time: Option[Time] = None,
    kind: Output.Kind = Output.Kind.writeln
  ): Unit = if (time.isEmpty || guard(time.get)) output(kind, msg)

  final def timeit[A](body: => A,
    message: Timing.Message[A] = Timing.no_message,
    enabled: Boolean = true,
    kind: Output.Kind = Output.Kind.warning
  ): A = Timing.timeit(body, message = message, enabled = enabled, output = apply(_, kind = kind))
}


class Console_Logger(override val guard_time: Time = Time.min, stdout: Boolean = false)
extends Logger {
  override def output(kind: Output.Kind, msg: => String): Unit =
    Output.output(Output.make_text(kind, msg), stdout = stdout)
  override def toString: String = if (stdout) "System.out" else "System.err"
}

class File_Logger(path: Path, override val guard_time: Time = Time.min)
extends Logger {
  override def output(kind: Output.Kind, msg: => String): Unit = synchronized {
    File.append(path, Output.make_text(kind, msg) + "\n")
  }
  override def toString: String = path.toString
}
