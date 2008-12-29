/*  Title:      Pure/General/event_bus.scala
    Author:     Makarius

Generic event bus.
*/

package isabelle

import scala.collection.jcl.LinkedList


class EventBus[Event] {
  type Handler = Event => Unit
  private val handlers = new LinkedList[Handler]

  def += (h: Handler) = synchronized { handlers -= h; handlers += h }
  def -= (h: Handler) = synchronized { handlers -= h }

  def event(e: Event) = synchronized { for(h <- handlers) h(e) }
}
