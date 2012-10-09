/*  Title:      Tools/Graphview/src/mutator_event.scala
    Author:     Markus Kaiser, TU Muenchen

Events for dialog synchronization.
*/

package isabelle.graphview


import isabelle._

import scala.collection.mutable

import java.awt.Color


object Mutator_Event
{
  type Mutator_Markup = (Boolean, Color, Mutator)

  sealed abstract class Message
  case class Add(m: Mutator_Markup) extends Message
  case class NewList(m: List[Mutator_Markup]) extends Message

  type Receiver = PartialFunction[Message, Unit]

  class Bus
  {
    private val receivers = new mutable.ListBuffer[Receiver]

    def += (r: Receiver) { Swing_Thread.require(); receivers += r }
    def -= (r: Receiver) { Swing_Thread.require(); receivers -= r }
    def event(x: Message) { Swing_Thread.require(); receivers.foreach(r => r(x)) }
  }
}