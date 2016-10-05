/*  Title:      Pure/System/progress.scala
    Author:     Makarius

Progress context for system processes.
*/

package isabelle


class Progress
{
  def echo(msg: String) {}
  def echo_if(cond: Boolean, msg: String) { if (cond) echo(msg) }
  def theory(session: String, theory: String) {}
  def stopped: Boolean = false
  override def toString: String = if (stopped) "Progress(stopped)" else "Progress"
}

object Ignore_Progress extends Progress

class Console_Progress(verbose: Boolean = false) extends Progress
{
  override def echo(msg: String) { Console.println(msg) }
  override def theory(session: String, theory: String): Unit =
    if (verbose) echo(session + ": theory " + theory)

  @volatile private var is_stopped = false
  def interrupt_handler[A](e: => A): A = POSIX_Interrupt.handler { is_stopped = true } { e }
  override def stopped: Boolean =
  {
    if (Thread.interrupted) is_stopped = true
    is_stopped
  }
}
