/*  Title:      Tools/VSCode/src/logger.scala
    Author:     Makarius

Minimal logging support.
*/

package isabelle.vscode


import isabelle._


object Logger
{
  def make(log_file: Option[Path]): Logger =
    log_file match { case Some(file) => new File_Logger(file) case None => No_Logger }
}

trait Logger
{
  def apply(msg: => String): Unit
}

object No_Logger extends Logger
{
  def apply(msg: => String) { }
}

class File_Logger(path: Path) extends Logger
{
  def apply(msg: => String) { synchronized { File.append(path, msg + "\n") } }

  override def toString: String = path.toString
}
