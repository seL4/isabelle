/*
 * Changes in text as event
 *
 * @author Johannes Hölzl, TU Munich
 */

package isabelle.proofdocument


object Text {
  case class Change(
    base_id: String,
    id: String,
    start: Int,
    added: String,
    removed: String) {
    override def toString = "start: " + start + " added: " + added + " removed: " + removed
  }
}