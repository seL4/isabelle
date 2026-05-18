/*  Title:      Pure/General/logger.scala
    Author:     Makarius

Minimal logging support.
*/

package isabelle


object Logger {
  val none: Logger = new Logger {
    override def toString: String = "Logger.none"
    override def output(kind: Output.Kind, msg: => String): Unit = ()
  }

  def make_file(
    log_path: Option[Path],
    guard_time: Time = Time.min,
    default: => Logger = none
  ): Logger =
    log_path match {
      case Some(file) => new File_Logger(file, guard_time)
      case None => default
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

  def make_system_log(
    progress: => Progress,
    options: Options,
    guard_time: Time = Time.min,
    default: => Logger = none
  ): Logger =
    options.string("system_log") match {
      case "" => default
      case "-" => make_progress(progress, guard_time = guard_time)
      case log_path => make_file(Some(Path.explode(log_path)), guard_time = guard_time)
    }
}

abstract class Logger {
  val guard_time: Time = Time.min
  def guard(t: Time): Boolean = t >= guard_time
  def output(kind: Output.Kind, msg: => String): Unit

  final def apply(
    msg: => String,
    time: Option[Time] = None,
    kind: Output.Kind = Output.Kind.writeln
  ): Unit = if (time.isEmpty || guard(time.get)) output(kind, msg)

  final def warning(msg: => String): Unit = apply(msg, kind = Output.Kind.warning)
  final def error_message(msg: => String): Unit = apply(msg, kind = Output.Kind.error_message)

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
  override def toString: String = if (stdout) "Console.out" else "Console.err"
}

class File_Logger(path: Path, override val guard_time: Time = Time.min)
extends Logger {
  override def output(kind: Output.Kind, msg: => String): Unit = synchronized {
    File.append(path, Output.make_text(kind, msg) + "\n")
  }
  override def toString: String = path.toString

  // touch file as file-system test
  File.append(path, "")
}
