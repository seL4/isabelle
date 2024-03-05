/*  Title:      Pure/General/logger.scala
    Author:     Makarius

Minimal logging support.
*/

package isabelle


object Logger {
  def make_file(log_file: Option[Path], guard_time: Time = Time.min): Logger =
    log_file match {
      case Some(file) => new File_Logger(file, guard_time)
      case None => No_Logger
    }

  def make_progress(progress: => Progress, guard_time: Time = Time.min): Logger =
    new Logger {
      override def output(msg: => String): Unit =
        if (progress != null) progress.echo(msg)
    }

  def make_system_log(progress: Progress, options: Options, guard_time: Time = Time.min): Logger =
    options.string("system_log") match {
      case "" => No_Logger
      case "-" => make_progress(progress, guard_time = guard_time)
      case log_file => make_file(Some(Path.explode(log_file)), guard_time = guard_time)
    }
}

trait Logger {
  val guard_time: Time = Time.min
  def guard(t: Time): Boolean = t >= guard_time
  def output(msg: => String): Unit = {}

  final def apply(msg: => String, time: Option[Time] = None): Unit =
    if (time.isEmpty || guard(time.get)) output(msg)

  final def timeit[A](body: => A,
    message: Exn.Result[A] => String = null,
    enabled: Boolean = true
  ): A = Timing.timeit(body, message = message, enabled = enabled, output = apply(_))
}

object No_Logger extends Logger

class File_Logger(path: Path, override val guard_time: Time = Time.min)
extends Logger {
  override def output(msg: => String): Unit = synchronized { File.append(path, msg + "\n") }
  override def toString: String = path.toString
}

class System_Logger(override val guard_time: Time = Time.min)
extends Logger {
  override def output(msg: => String): Unit = synchronized {
    if (Platform.is_windows) System.out.println(msg)
    else System.console.writer.println(msg)
  }
}
