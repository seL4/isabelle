/*  Title:      Pure/General/event_bus.scala
    Author:     Makarius

Generic event bus.
*/

package isabelle

import scala.collection.mutable.ListBuffer


class EventBus[Event] {
  type Handler = Event => Unit
  private val handlers = new ListBuffer[Handler]

  def += (h: Handler) = synchronized { handlers += h }
  def + (h: Handler) = { this += h; this }

  def -= (h: Handler) = synchronized { handlers -= h }
  def - (h: Handler) = { this -= h; this }

  def event(e: Event) = synchronized { handlers.toList } foreach (h => h(e))
}
