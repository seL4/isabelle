/*  Title:      Pure/General/event_bus.scala
    Author:     Makarius

Generic event bus with multiple handlers and optional exception
logging.
*/

package isabelle

import scala.collection.mutable.ListBuffer


class EventBus[Event]
{
  /* event handlers */

  type Handler = Event => Unit
  private val handlers = new ListBuffer[Handler]

  def += (h: Handler) = synchronized { handlers += h }
  def + (h: Handler) = { this += h; this }

  def -= (h: Handler) = synchronized { handlers -= h }
  def - (h: Handler) = { this -= h; this }


  /* event invocation */

  var logger: Throwable => Unit = throw _

  def event(x: Event) = {
    val log = logger
    for (h <- synchronized { handlers.toList }) {
      try { h(x) }
      catch { case e: Throwable => log(e) }
    }
  }
}
