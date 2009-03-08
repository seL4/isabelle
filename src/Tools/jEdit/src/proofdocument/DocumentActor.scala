/*
 * Managing changes on ProofDocuments via Actors
 *
 * @author Fabian Immler, TU Munich
 */

package isabelle.proofdocument

import scala.actors.Actor
import scala.actors.Actor._
import isabelle.utils.LinearSet

object DocumentActor {
  case class Activate
  case class SetEventBus(bus: EventBus[StructureChange])
  case class SetIsCommandKeyword(is_command_keyword: String => Boolean)
}
class DocumentActor extends Actor {
  private var versions = List(
    new ProofDocument(LinearSet.empty, LinearSet.empty, false, _ => false, new EventBus))

  def get = versions.head
  
  def act() {
    import DocumentActor._
    loop {
      react {
        case Activate => versions ::= versions.head.activate
        case SetEventBus(bus) => versions ::= versions.head.set_event_bus(bus)
        case SetIsCommandKeyword(f) => versions ::= versions.head.set_command_keyword(f)
        case change: Text.Change => versions ::= versions.head.text_changed(change)
      }
    }
  }
}
