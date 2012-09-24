/*  Title:      Tools/Graphview/src/mutator_event.scala
    Author:     Markus Kaiser, TU Muenchen

Events for dialog synchronization.
*/

package isabelle.graphview


import java.awt.Color


object Mutator_Event
{
  type Key = String
  type Entry = Option[Locale]
  type Mutator_Markup = (Boolean, Color, Mutator[Key, Entry])
  
  sealed abstract class Message
  case class Add(m: Mutator_Markup) extends Message
  case class NewList(m: List[Mutator_Markup]) extends Message
}