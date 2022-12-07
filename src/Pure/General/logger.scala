/*  Title:      Pure/General/logger.scala
    Author:     Makarius

Minimal logging support.
*/

package isabelle


object Logger {
  def make(log_file: Option[Path]): Logger =
    log_file match { case Some(file) => new File_Logger(file) case None => No_Logger }

  def make(progress: Progress): Logger =
    new Logger { def apply(msg: => String): Unit = progress.echo(msg) }
}

trait Logger {
  def apply(msg: => String): Unit

  def timeit_result[A](
    message: Exn.Result[A] => String = null,
    enabled: Boolean = true
  )(e: => A): A = Timing.timeit_result(message, enabled, apply(_))(e)

  def timeit[A](message: String = "", enabled: Boolean = true)(e: => A) =
    timeit_result(_ => message, enabled)
}

object No_Logger extends Logger {
  def apply(msg: => String): Unit = {}
}

class File_Logger(path: Path) extends Logger {
  def apply(msg: => String): Unit = synchronized { File.append(path, msg + "\n") }

  override def toString: String = path.toString
}
