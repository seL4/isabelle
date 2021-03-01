/*  Title:      Tools/Graphview/mutator_event.scala
    Author:     Markus Kaiser, TU Muenchen
    Author:     Makarius

Events for dialog synchronization.
*/

package isabelle.graphview


import isabelle._


object Mutator_Event
{
  sealed abstract class Message
  case class Add(m: Mutator.Info) extends Message
  case class New_List(m: List[Mutator.Info]) extends Message

  type Receiver = PartialFunction[Message, Unit]

  class Bus
  {
    private val receivers = Synchronized[List[Receiver]](Nil)

    def += (r: Receiver): Unit = receivers.change(Library.insert(r))
    def -= (r: Receiver): Unit = receivers.change(Library.remove(r))
    def event(x: Message): Unit = receivers.value.reverse.foreach(r => r(x))
  }
}