/*  Title:      Tools/Graphview/mutator_event.scala
    Author:     Markus Kaiser, TU Muenchen
    Author:     Makarius

Events for dialog synchronization.
*/

package isabelle.graphview


import isabelle._

import scala.collection.mutable

import java.awt.Color


object Mutator_Event
{
  sealed abstract class Message
  case class Add(m: Mutator.Info) extends Message
  case class New_List(m: List[Mutator.Info]) extends Message

  type Receiver = PartialFunction[Message, Unit]

  class Bus
  {
    private val receivers = new mutable.ListBuffer[Receiver]

    def += (r: Receiver) { GUI_Thread.require {}; receivers += r }
    def -= (r: Receiver) { GUI_Thread.require {}; receivers -= r }
    def event(x: Message) { GUI_Thread.require {}; receivers.foreach(r => r(x)) }
  }
}