/*  Title:      Pure/System/event_bus.scala
    Author:     Makarius

Generic event bus with multiple receiving actors.
*/

package isabelle

import scala.actors.Actor, Actor._
import scala.collection.mutable.ListBuffer


class Event_Bus[Event]
{
  /* receivers */

  private val receivers = new ListBuffer[Actor]

  def += (r: Actor) { synchronized { receivers += r } }
  def + (r: Actor): Event_Bus[Event] = { this += r; this }

  def += (f: Event => Unit) {
    this += actor { loop { react { case x => f(x.asInstanceOf[Event]) } } }
  }

  def + (f: Event => Unit): Event_Bus[Event] = { this += f; this }

  def -= (r: Actor) { synchronized { receivers -= r } }
  def - (r: Actor) = { this -= r; this }


  /* event invocation */

  def event(x: Event) { synchronized { receivers.foreach(_ ! x) } }
}
