/*  Title:      Pure/Concurrent/delay.scala
    Author:     Makarius

Delayed events.
*/

package isabelle


class Delay_Ops(log: Logger) {
  override def toString: String = "Delay(" + log.toString + ")"

  protected def app(body: => Unit): Unit = body

  // delayed event after first invocation
  def first(delay: => Time)(event: => Unit): Delay = new Delay(true, delay, log, app, event)

  // delayed event after last invocation
  def last(delay: => Time)(event: => Unit): Delay = new Delay(false, delay, log, app, event)
}

final class Delay(
  first: Boolean,
  delay: => Time,
  log: Logger,
  app: (=> Unit) => Unit,
  event: => Unit
) {
  private var running: Option[Event_Timer.Request] = None

  private def run(): Unit = {
    val do_run = synchronized {
      if (running.isDefined) { running = None; true } else false
    }
    if (do_run) app(event)
  }

  def invoke(msg: String = ""): Unit = synchronized {
    if (msg.nonEmpty) log.warning("Delay.invoke " + msg)
    val new_run =
      running match {
        case Some(request) => if (first) false else { request.cancel(); true }
        case None => true
      }
    if (new_run) {
      running = Some(Event_Timer.request(Time.now() + delay, log = log)(run()))
    }
  }

  def revoke(msg: String = ""): Unit = synchronized {
    if (msg.nonEmpty) log.warning("Delay.revoke " + msg)
    running match {
      case Some(request) => request.cancel(); running = None
      case None =>
    }
  }

  def postpone(alt_delay: Time, msg: String = ""): Unit = synchronized {
    if (msg.nonEmpty) log.warning("Delay.postpone " + msg)
    running match {
      case Some(request) =>
        val alt_time = Time.now() + alt_delay
        if (request.time < alt_time && request.cancel()) {
          running = Some(Event_Timer.request(alt_time, log = log)(run()))
        }
      case None =>
    }
  }
}
