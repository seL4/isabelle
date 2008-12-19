/*
 * Event sources with multiple handlers
 *
 * @author Johannes Hölzl, TU Munich
 */

package isabelle.utils

import scala.collection.mutable.HashSet

class EventSource[Event] {
  private val handlers = new HashSet[(Event) => Unit]()

  def add(handler : (Event) => Unit) { handlers += handler }
  def remove(handler : (Event) => Unit) { handlers -= handler }
	
  def fire(event : Event) { for(h <- handlers) h(event) }
}