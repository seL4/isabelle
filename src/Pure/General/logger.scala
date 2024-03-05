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
      override val guard_time: Time = t
      override def output(msg: => String): Unit =
        if (progress != null) progress.echo(msg)
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
  def output(msg: => String): Unit = {}

  final def apply(msg: => String, time: Option[Time] = None): Unit =
    if (time.isEmpty || guard(time.get)) output(msg)

  final def timeit[A](body: => A,
    message: Exn.Result[A] => String = null,
    enabled: Boolean = true
  ): A = Timing.timeit(body, message = message, enabled = enabled, output = apply(_))
}

class File_Logger(path: Path, override val guard_time: Time = Time.min)
extends Logger {
  override def output(msg: => String): Unit = synchronized { File.append(path, msg + "\n") }
  override def toString: String = path.toString
}

class System_Logger(override val guard_time: Time = Time.min)
extends Logger {
  override def output(msg: => String): Unit = synchronized {
    if (System.console != null && System.console.writer != null) {
      System.console.writer.println(msg)
      System.console.writer.flush()
    }
    else if (System.out != null) {
      System.out.println(msg)
      System.out.flush()
    }
  }
}
