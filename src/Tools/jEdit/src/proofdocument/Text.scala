/*
 * Changes in text as event
 *
 * @author Johannes Hölzl, TU Munich
 */

package isabelle.proofdocument


object Text {
  case class Change(id: String, start: Int, val added: String, val removed: String) {
    override def toString = "start: " + start + " added: " + added + " removed: " + removed
  }
}