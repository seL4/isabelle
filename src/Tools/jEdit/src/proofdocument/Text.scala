/*
 * Text as event source
 *
 * @author Johannes Hölzl, TU Munich
 */

package isabelle.proofdocument


object Text {
  case class Change(start: Int, val added: String, val removed: Int) {
    override def toString = "start: " + start + " added: " + added + " removed: " + removed
  }
}

trait Text {
  def changes: EventBus[Text.Change]
}
