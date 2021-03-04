/*  Title:      Pure/Concurrent/delay.scala
    Author:     Makarius

Delayed events.
*/

package isabelle


object Delay
{
  // delayed event after first invocation
  def first(delay: => Time, log: Logger = No_Logger, gui: Boolean = false)(event: => Unit): Delay =
    new Delay(true, delay, log, if (gui) GUI_Thread.later { event } else event )

  // delayed event after last invocation
  def last(delay: => Time, log: Logger = No_Logger, gui: Boolean = false)(event: => Unit): Delay =
    new Delay(false, delay, log, if (gui) GUI_Thread.later { event } else event )
}

final class Delay private(first: Boolean, delay: => Time, log: Logger, event: => Unit)
{
  private var running: Option[Event_Timer.Request] = None

  private def run: Unit =
  {
    val do_run = synchronized {
      if (running.isDefined) { running = None; true } else false
    }
    if (do_run) {
      try { event }
      catch { case exn: Throwable if !Exn.is_interrupt(exn) => log(Exn.message(exn)); throw exn }
    }
  }

  def invoke(): Unit = synchronized
  {
    val new_run =
      running match {
        case Some(request) => if (first) false else { request.cancel(); true }
        case None => true
      }
    if (new_run)
      running = Some(Event_Timer.request(Time.now() + delay)(run))
  }

  def revoke(): Unit = synchronized
  {
    running match {
      case Some(request) => request.cancel(); running = None
      case None =>
    }
  }

  def postpone(alt_delay: Time): Unit = synchronized
  {
    running match {
      case Some(request) =>
        val alt_time = Time.now() + alt_delay
        if (request.time < alt_time && request.cancel()) {
          running = Some(Event_Timer.request(alt_time)(run))
        }
      case None =>
    }
  }
}
