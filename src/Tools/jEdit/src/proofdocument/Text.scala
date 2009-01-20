/*
 * Text as event source
 *
 * @author Johannes Hölzl, TU Munich
 */

package isabelle.proofdocument


object Text {
  case class Changed(val start: Int, val added: Int, val removed: Int)
}

trait Text {
  def content(start: Int, stop: Int): String
  def length: Int
  def changes: EventBus[Text.Changed]
}
