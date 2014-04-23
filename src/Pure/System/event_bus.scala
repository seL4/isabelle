/*  Title:      Pure/System/event_bus.scala
    Module:     PIDE
    Author:     Makarius

Generic event bus with multiple receiving actors.
*/

package isabelle


import scala.actors.Actor, Actor._


class Event_Bus[Event]
{
  /* receivers */

  private val receivers = Synchronized(List.empty[Actor])

  def += (r: Actor) { receivers >> (rs => Library.insert(r, rs)) }

  def += (f: Event => Unit) {
    this += actor { loop { react { case x => f(x.asInstanceOf[Event]) } } }
  }

  def -= (r: Actor) { receivers >> (rs => Library.remove(r, rs)) }


  /* event invocation */

  def event(x: Event) { receivers().reverseIterator.foreach(_ ! x) }
}
